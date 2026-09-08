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

variable {k G H : Type*} [Semiring k] [Monoid G] [Monoid H] (φ : G →* H) {A B : Type*}
  [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B] (σ : Representation k G A)
  (ρ : Representation k G B)

/--
If `ρ : Representation k G A` and `φ : G →* H` then `coindV φ ρ` is the sub-`k`-module of
functions `H → A` underlying the coinduction of `ρ` along `φ`, i.e., the functions `f : H → A`
such that `f (φ g * h) = (ρ g) (f h)` for all `g : G` and `h : H`.
-/
@[simps]
/-
**Representation.coindV** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：coindV : Submodule k (H -> A) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ρ : Representation k G A` and `φ : G →* H` then `coindV φ ρ` is the sub-`k`-
module of
functions `H → A` underlying the coinduction of `ρ` along `φ`, i.e., the functio
ns `f : H → A`
such that `f (φ g * h) = (ρ g) (f h)` for all `g : G` and `h : H`.
-/
def coindV : Submodule k (H → A) where
  carrier := {f : H → A | ∀ (g : G) (h : H), f (φ g * h) = σ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

@[simp]
/-
**Representation.mem_coindV** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：mem_coindV (f : H -> A) : f in coindV φ σ ↔ forall (g : G) (h : H), f (φ g
 * h) = σ g (f h)
参数：f : H -> A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_coindV (f : H → A) : f ∈ coindV φ σ ↔ ∀ (g : G) (h : H), f (φ g * h) = σ g (f h) :=
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
/-
**Representation.coind** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：coind : Representation k H (coindV φ ρ) where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ρ : Representation k G A` and `φ : G →* H` then `coind φ ρ` is the represent
ation
coinduced by `ρ` along `φ`, defined as the following action of `H` on the submod
ule `coindV φ ρ`
of `G`-equivariant functions from `H` to `A`: we let `h : H` send the function `
f : H → A`
to the function sending `h₁` to `f (h₁ * h)`.

See also `Rep.coind` and `Representation.coind'` for variants involving the cate
gory `Rep k G`.
-/
def coind : Representation k H (coindV φ ρ) where
  toFun h := (LinearMap.funLeft _ _ (· * h)).restrict fun x hx g h₁ => by
    simpa [mul_assoc] using hx g (h₁ * h)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
variable {σ ρ} in
/-- Given a monoid homomorphism `φ : G →* H` and an intertwining map `f : σ ⟶ ρ`, there is a
  natural intertwining map `coind φ σ ⟶ coind φ ρ` given by postcomposition by `f`. -/
/-
**Representation.coindMap** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：coindMap (f : σ.IntertwiningMap ρ) : (coind φ σ).IntertwiningMap (coind φ 
ρ) where __ : _ ->ₗ[k] _
参数：f : σ.IntertwiningMap ρ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : G →* H` and an intertwining map `f : σ ⟶ ρ`, th
ere is a
  natural intertwining map `coind φ σ ⟶ coind φ ρ` given by postcomposition by `
f`.
-/
def coindMap (f : σ.IntertwiningMap ρ) : (coind φ σ).IntertwiningMap (coind φ ρ) where
  __ : _ →ₗ[k] _ := (f.toLinearMap.compLeft H).restrict fun x h ↦ by
    simp only [mem_coindV, LinearMap.compLeft_apply, Function.comp_apply,
      IntertwiningMap.toLinearMap_apply] at h ⊢
    intro g h0
    simpa [h] using LinearMap.ext_iff.1 (f.2 g) (x h0)
  isIntertwining' h := by ext; simp
/-
**Representation.coindMap_coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：coindMap_coe_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) : (coindMap 
φ f) x = (f.toLinearMap.compLeft H) x
参数：f : σ.IntertwiningMap ρ；x : coindV φ σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coindMap_coe_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) :
    (coindMap φ f) x = (f.toLinearMap.compLeft H) x := rfl

@[simp]
/-
**Representation.coindMap_coe_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Representat
ion`。
形式化陈述：coindMap_coe_apply_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) (h : H
) : ((coindMap φ f) x).1 h = f (x.1 h)
参数：f : σ.IntertwiningMap ρ；x : coindV φ σ；h : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coindMap_coe_apply_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) (h : H) :
    ((coindMap φ f) x).1 h = f (x.1 h) := rfl

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Monoid G] [Monoid H]
  (φ : G →* H) (A : Rep k G)

section Coind

/--
If `φ : G →* H` and  `A : Rep k G` then `coind φ A` is the coinduction of `A` along `φ`,
defined by letting `H` act on the `G`-equivariant functions `H → A` by `(h • f) h₁ := f (h₁ * h)`.
-/
/-
**Rep.coind** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：coind : Rep k H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : G →* H` and  `A : Rep k G` then `coind φ A` is the coinduction of `A` al
ong `φ`,
defined by letting `H` act on the `G`-equivariant functions `H → A` by `(h • f) 
h₁ := f (h₁ * h)`.
-/
noncomputable abbrev coind : Rep k H := Rep.of (Representation.coind φ A.ρ)

/-- Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : A ⟶ B`, there
is a natural `H`-representation morphism `coind φ A ⟶ coind φ B`, given by postcomposition by
`f`. -/
/-
**Rep.coindMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：coindMap {A B : Rep k G} (f : A ⟶ B) : coind φ A ⟶ coind φ B
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : 
A ⟶ B`, there
is a natural `H`-representation morphism `coind φ A ⟶ coind φ B`, given by postc
omposition by
`f`.
-/
noncomputable abbrev coindMap {A B : Rep k G} (f : A ⟶ B) : coind φ A ⟶ coind φ B :=
  ofHom <| Representation.coindMap φ f.hom

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind φ A`, with action on maps given by postcomposition. -/
@[implicit_reducible, simps obj map]
/-
**Rep.coindFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindFunctor : Rep.{t} k G ⥤ Rep k H where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-repr
esentation `A`
to the coinduced `H`-representation `coind φ A`, with action on maps given by po
stcomposition.
-/
noncomputable def coindFunctor : Rep.{t} k G ⥤ Rep k H where
  obj A := coind φ A
  map f := coindMap φ f
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
    refine ⟨⟨x, fun _ _ => ?_⟩, Subtype.ext <| funext fun g => ?_⟩
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
/-
**Rep._root_.Representation.coind'** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` alon
g `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-e
quivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
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
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` along `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-equivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
/-
**Rep.coind'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：coind' : Rep k H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` alon
g `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-e
quivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
noncomputable abbrev coind' : Rep k H := Rep.of (Representation.coind' φ A)

variable {A} in
@[ext]
/-
**Rep.coind'_ext** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} {H : Type w} [inst : CommRing k] [inst_1 : Mon
oid G] [inst_2 : Monoid H] (φ : G →* H)   {A : Rep.{max u w, u, v} k G} {f g : ↑
(Rep.coind' φ A)},   (∀ (h : H),       (Rep.Hom.hom f).toLinearMap (MonoidAlgebr
a.single h 1) = (Rep.Hom.hom g).toLinearMap (MonoidAlgebra.single h 1)) →     f 
= g
参数：φ : G →* H；Rep.coind' φ A；∀ (h : H),       (Rep.Hom.hom f).toLinearMap (Monoi
dAlgebra.single h 1) = (Rep.Hom.hom g).toLinearMap (MonoidAlgebra.single h 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用引理 `MonoidAlgebra.lhom_ext'`：lhom_ext' {N : Type*} [Semiring R] [AddCommMono
id N] [Module R N] [Module R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), Linea
rMap.comp f (…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
lemma coind'_ext {f g : coind' φ A} (hfg : ∀ h, f.hom.toLinearMap (.single h 1) =
    g.hom.toLinearMap (.single h 1)) : f = g :=
  Rep.hom_ext <| by ext1; dsimp; ext h; simpa using hfg h

/-- Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : A ⟶ B`, there
is a natural `H`-representation morphism `coind' φ A ⟶ coind' φ B`, given by postcomposition
by `f`. -/
/-
**Rep.coindMap'** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindMap' {A B : Rep k G} (f : A ⟶ B) : coind' φ A ⟶ coind' φ B
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : 
A ⟶ B`, there
is a natural `H`-representation morphism `coind' φ A ⟶ coind' φ B`, given by pos
tcomposition
by `f`.
-/
noncomputable def coindMap' {A B : Rep k G} (f : A ⟶ B) : coind' φ A ⟶ coind' φ B := Rep.ofHom
  { __ := Linear.rightComp k _ f
    isIntertwining' h := by ext; simp }

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind' φ A`, with action on maps given by postcomposition. -/
@[implicit_reducible, simps obj map]
/-
**Rep.coindFunctor'** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindFunctor' : Rep k G ⥤ Rep k H where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-repr
esentation `A`
to the coinduced `H`-representation `coind' φ A`, with action on maps given by p
ostcomposition.
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
/-
**Rep.coindVEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindVEquiv : A.ρ.coindV φ ≃ₗ[k] (res φ (leftRegular k H) ⟶ A) where toFun
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : G →* H` and `A : Rep k G` then the `k`-submodule of functions `f : H → A
`
such that for all `g : G`, `h : H`, `f (φ g * h) = A.ρ g (f h)`, is `k`-linearly
 equivalent
to the `G`-representation morphisms `k[H] ⟶ A`.
-/
noncomputable def coindVEquiv :
    A.ρ.coindV φ ≃ₗ[k] (res φ (leftRegular k H) ⟶ A) where
  toFun f := Rep.ofHom ⟨linearCombination _ f.1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g ↦ by dsimp; ext; simp [f.2 g]⟩
  map_add' _ _ := coind'_ext φ <| by simp [Rep.add_hom]
  map_smul' _ _ := coind'_ext φ <| by simp [smul_hom]
  invFun f := ⟨fun h ↦ f.hom.toLinearMap (.single h 1), fun g h ↦ by
    simp only [res_obj_V, res_obj_ρ, Representation.IntertwiningMap.toLinearMap_apply]
    have := by simpa using (hom_comm_apply f g (.single h 1)).symm
    rw [← this]⟩
  left_inv x := by simp
  right_inv x := coind'_ext φ fun _ => by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- `coind φ A` and `coind' φ A` are isomorphic representations, with the underlying
`k`-linear equivalence given by `coindVEquiv`. -/
/-
**Rep.coindIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindIso : coind φ A ≅ coind' φ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coind φ A` and `coind' φ A` are isomorphic representations, with the underlying
`k`-linear equivalence given by `coindVEquiv`.
-/
noncomputable def coindIso : coind φ A ≅ coind' φ A :=
  Rep.mkIso <| .mk (coindVEquiv φ A) fun h => by ext; simp [homEquiv]

/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functors `Rep k G ⥤ Rep k H` given by
`coindFunctor k φ` and `coindFunctor' k φ` are naturally isomorphic, with isomorphism on objects
given by `coindIso φ`. -/
@[simps!]
/-
**Rep.coindFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coindFunctorIso : coindFunctor k φ ≅ coindFunctor' k φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : G →* H`, the coinduction functors `Rep k G ⥤ Re
p k H` given by
`coindFunctor k φ` and `coindFunctor' k φ` are naturally isomorphic, with isomor
phism on objects
given by `coindIso φ`.
-/
noncomputable def coindFunctorIso : coindFunctor k φ ≅ coindFunctor' k φ :=
  NatIso.ofComponents (coindIso φ) fun _ => by
    ext
    exact coind'_ext _ fun _ ↦ by simp [coindIso, coindMap']

end CoindIso

noncomputable section Adjunction

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism induced by the adjunction between `res φ` and `coind φ` sending a morphism
  `f : res φ B ⟶ A` to the morphism `B ⟶ coind φ A` given by the underlying linear map sending
  `b : B.V` to the function sending `h : H` to `f ((B.ρ h) b)`. -/
/-
**Rep.resCoindToHom** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：resCoindToHom (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) : B ⟶ (coind φ
 A)
参数：B : Rep k H；A : Rep k G；f : res φ B ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism induced by the adjunction between `res φ` and `coind φ` sending a m
orphism
  `f : res φ B ⟶ A` to the morphism `B ⟶ coind φ A` given by the underlying line
ar map sending
  `b : B.V` to the function sending `h : H` to `f ((B.ρ h) b)`.
-/
def resCoindToHom (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) : B ⟶ (coind φ A) :=
  Rep.ofHom ⟨(LinearMap.pi fun h => f.hom.toLinearMap ∘ₗ
    Rep.ρ B h).codRestrict _ fun _ _ _ => by simpa using hom_comm_apply f _ _, fun g ↦ by
    dsimp; ext; simp⟩

@[simp]
/-
**Rep.resCoindToHom_hom_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resCoindToHom_hom_apply_coe (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) 
(c : ↑B.V) (i : H) : (DFunLike.coe (F
参数：B : Rep k H；A : Rep k G；f : res φ B ⟶ A；c : ↑B.V；i : H。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Rep.resCoindHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：resCoindHomEquiv (B : Rep.{max w t} k H) (A : Rep.{max w t} k G) : (res φ 
B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A) where toFun f
参数：B : Rep.{max w t} k H；A : Rep.{max w t} k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-r
epresentation
`A`, there is a `k`-linear equivalence between the `G`-representation morphisms 
`res φ B ⟶ A` and
the `H`-representation morphisms `B ⟶ coind φ A`.

Note `Rep.resCoindHomEquiv.{t, u, v, w}` has the property that
even with all inputs explicitly given, the first universe cannot be synthesized.
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
/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functor `Rep k G ⥤ Rep k H` is right
adjoint to the restriction functor along `φ`. -/
/-
**Rep.resCoindAdjunction** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：resCoindAdjunction : resFunctor.{max w t} φ ⊣ coindFunctor k φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monoid homomorphism `φ : G →* H`, the coinduction functor `Rep k G ⥤ Rep
 k H` is right
adjoint to the restriction functor along `φ`.
-/
noncomputable abbrev resCoindAdjunction : resFunctor.{max w t} φ ⊣ coindFunctor k φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (coindFunctor.{max w t} k φ).IsRightAdjoint :=
  (resCoindAdjunction k φ).isRightAdjoint
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (resFunctor.{max w t} (k := k) φ).IsLeftAdjoint :=
  (resCoindAdjunction k φ).isLeftAdjoint
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Type w} [Group G] (S : Subgroup G) :
    (resFunctor.{max w t} (k := k) S.subtype).PreservesProjectiveObjects :=
  (resFunctor S.subtype).preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (resCoindAdjunction k S.subtype)

end Adjunction
end Rep

