/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal closed structure on `Module R`.
-/

@[expose] public section

universe v w x u

open CategoryTheory Opposite

namespace ModuleCat

variable {R : Type u} [CommRing R]

/--
Definition of `monoidalClosedHomEquiv` / `monoidalClosedHomEquiv` 的定义

English:
definition monoidalClosedHomEquiv
  signature: (M N P : ModuleCat.{u} R)
  body: ofHom₂ LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ ofHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    solve_by_elim

中文:
定义 monoidalClosedHomEquiv
  签名: (M N P : 模范畴.{u} R)
  定义体: ofHom₂ LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ ofHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    solve_by_elim

Depends on / 依赖: LinearMap, LinearMap.compr, TensorProduct, TensorProduct.mk
-/
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
toFun f := ofHom₂ LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ ofHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    solve_by_elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalClosed (ModuleCat.{u} R)
  body: { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              -- Porting note: this proof was automatic in mathlib3
              homEquiv_naturality_left_symm := by
                i

中文:
实例 :
  签名: 幺半群闭 (模范畴.{u} R)
  定义体: { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              -- Porting note: this proof was automatic in mathlib3
              homEquiv_naturality_left_symm := by
                i

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, ConcreteCategory, ConcreteCategory.hom_injective, Function, Function.Injective.addCommGroup, Hom.hom, Injective, ModuleCat, addCommGroup, homEquiv, hom_injective, linearCoyoneda, mkOfHomEquiv, monoidalClosedHomEquiv, rightAdj
-/
instance : MonoidalClosed (ModuleCat.{u} R) where
  closed M :=
    { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              -- Porting note: this proof was automatic in mathlib3
              homEquiv_naturality_left_symm := by
                intros
                ext : 1
                apply TensorProduct.ext'
                intro m n
                rfl } }

/--
theorem `ihom_map_apply` / 定理 `ihom_map_apply`

English:
theorem ihom_map_apply
  given: {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N))
  proof: rfl

中文:
定理 ihom_map_apply
  条件: {M N P : 模范畴.{u} R} (f : N ⟶ P) (g : 模范畴.of R (M ⟶ N))
  证明: rfl
-/
theorem ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N)) :
    (ihom M).map f g = g ≫ f :=
  rfl

open MonoidalCategory

/--
theorem `monoidalClosed_curry` / 定理 `monoidalClosed_curry`

English:
theorem monoidalClosed_curry
  given: {M N P : ModuleCat.{u} R} (f : M otimes N ⟶ P) (x : M) (y : N)
  proof: rfl

@[simp]

中文:
定理 monoidalClosed_curry
  条件: {M N P : 模范畴.{u} R} (f : M otimes N ⟶ P) (x : M) (y : N)
  证明: rfl

@[simp]

Depends on / 依赖: F.obj
-/
theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M otimes N ⟶ P) (x : M) (y : N) :
    ((MonoidalClosed.curry f).hom y).hom x = f (x otimesₜ[R] y) :=
  rfl

@[simp]
/--
theorem `monoidalClosed_uncurry` / 定理 `monoidalClosed_uncurry`

English:
theorem monoidalClosed_uncurry
  proof: rfl

中文:
定理 monoidalClosed_uncurry
  证明: rfl
-/
theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x otimesₜ[R] y) = (f y).hom x :=
  rfl

/--
theorem `ihom_ev_app` / 定理 `ihom_ev_app`

English:
theorem ihom_ev_app
  given: (M N : ModuleCat.{u} R)
  proof: by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  ext : 1
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry

中文:
定理 ihom_ev_app
  条件: (M N : 模范畴.{u} R)
  证明: by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  ext : 1
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry

Depends on / 依赖: MonoidalClosed, MonoidalClosed.uncurry_id_eq_ev, TensorProduct, TensorProduct.ext, monoidalClosed_uncurry, uncurry_id_eq_ev
-/
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = ModuleCat.ofHom (TensorProduct.uncurry (.id R) M ((ihom M).obj N) N
      (LinearMap.lcomp _ _ homLinearEquiv.toLinearMap ∘ₗ LinearMap.id.flip)) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  ext : 1
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ihom_coev_app` / 定理 `ihom_coev_app`

English:
theorem ihom_coev_app
  given: (M N : ModuleCat.{u} R)
  proof: rfl

中文:
定理 ihom_coev_app
  条件: (M N : 模范畴.{u} R)
  证明: rfl
-/
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = ModuleCat.ofHom₂ (TensorProduct.mk _ _ _).flip :=
  rfl

/--
theorem `monoidalClosed_pre_app` / 定理 `monoidalClosed_pre_app`

English:
theorem monoidalClosed_pre_app
  given: {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M)
  proof: rfl

中文:
定理 monoidalClosed_pre_app
  条件: {M N : 模范畴.{u} R} (P : 模范畴.{u} R) (f : N ⟶ M)
  证明: rfl
-/
theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = ofHom (homLinearEquiv.symm.toLinearMap ∘ₗ
      LinearMap.lcomp _ _ f.hom ∘ₗ homLinearEquiv.toLinearMap) :=
  rfl

end ModuleCat
