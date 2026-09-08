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

/-- Auxiliary definition for the `MonoidalClosed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking.)
-/
/-
**ModuleCat.monoidalClosedHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) : ((MonoidalCategory.tens
orLeft M).obj N ⟶ P) ≃ (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P)
 where toFun f
参数：M N P : ModuleCat.{u} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalClosed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking.)
-/
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
  toFun f := ofHom₂ <| LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ ofHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    solve_by_elim
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**ModuleCat.ihom_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (
M ⟶ N)) : (ihom M).map f g = g ≫ f
参数：f : N ⟶ P；g : ModuleCat.of R (M ⟶ N)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_map_apply {M N P : ModuleCat.{u} R} (f : N ⟶ P) (g : ModuleCat.of R (M ⟶ N)) :
    (ihom M).map f g = g ≫ f :=
  rfl

open MonoidalCategory
/-
**ModuleCat.monoidalClosed_curry** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M otimes N ⟶ P) (x : M
) (y : N) : ((MonoidalClosed.curry f).hom y).hom x = f (x otimesₜ[R] y)
参数：f : M otimes N ⟶ P；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monoidalClosed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    ((MonoidalClosed.curry f).hom y).hom x = f (x ⊗ₜ[R] y) :=
  rfl

@[simp]
/-
**ModuleCat.monoidalClosed_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：monoidalClosed_uncurry {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u
} R] P) (x : M) (y : N) : MonoidalClosed.uncurry f (x otimesₜ[R] y) = (f y).hom 
x
参数：f : N ⟶ M ⟶[ModuleCat.{u} R] P；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) = (f y).hom x :=
  rfl

/-- Describes the counit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this
should give a map `M ⊗ Hom(M, N) ⟶ N`, so we flip the order of the arguments in the identity map
`Hom(M, N) ⟶ (M ⟶ N)` and uncurry the resulting map `M ⟶ Hom(M, N) ⟶ N.` -/
/-
**ModuleCat.ihom_ev_app** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：ihom_ev_app (M N : ModuleCat.{u} R) : (ihom.ev M).app N = ModuleCat.ofHom 
(TensorProduct.uncurry (.id R) M ((ihom M).obj N) N (LinearMap.lcomp _ _ homLine
arEquiv.toLinearMap ∘ₗ LinearMap.id.flip))
参数：M N : ModuleCat.{u} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `ModuleCat.Algebra.instSMulCommClassCarrier`：∀ {S₀ : Type u₀} [inst : Com
mSemiring S₀] {S : Type u} [inst_1 : Ring S] [inst_2 : Algebra S₀ S] {M : Module
Cat S},   SMulCommClass S S₀ ↑M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`：uncurry_id_eq_ev : uncur
ry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `ModuleCat.monoidalClosed_uncurry`：monoidalClosed_uncurry {M N P : Module
Cat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) : MonoidalClosed.unc
urry f (x otimesₜ[R] y…

--- 原说明 ---
Describes the counit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module 
`N` this
should give a map `M ⊗ Hom(M, N) ⟶ N`, so we flip the order of the arguments in 
the identity map
`Hom(M, N) ⟶ (M ⟶ N)` and uncurry the resulting map `M ⟶ Hom(M, N) ⟶ N.`
-/
theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = ModuleCat.ofHom (TensorProduct.uncurry (.id R) M ((ihom M).obj N) N
      (LinearMap.lcomp _ _ homLinearEquiv.toLinearMap ∘ₗ LinearMap.id.flip)) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  ext : 1
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry

set_option backward.isDefEq.respectTransparency false in
/-- Describes the unit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N` this should
define a map `N ⟶ Hom(M, M ⊗ N)`, which is given by flipping the arguments in the natural
`R`-bilinear map `M ⟶ N ⟶ M ⊗ N`. -/
/-
**ModuleCat.ihom_coev_app** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：ihom_coev_app (M N : ModuleCat.{u} R) : (ihom.coev M).app N = ModuleCat.of
Hom₂ (TensorProduct.mk _ _ _).flip
参数：M N : ModuleCat.{u} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Describes the unit of the adjunction `M ⊗ - ⊣ Hom(M, -)`. Given an `R`-module `N
` this should
define a map `N ⟶ Hom(M, M ⊗ N)`, which is given by flipping the arguments in th
e natural
`R`-bilinear map `M ⟶ N ⟶ M ⊗ N`.
-/
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = ModuleCat.ofHom₂ (TensorProduct.mk _ _ _).flip :=
  rfl
/-
**ModuleCat.monoidalClosed_pre_app** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : 
N ⟶ M) : (MonoidalClosed.pre f).app P = ofHom (homLinearEquiv.symm.toLinearMap ∘
ₗ LinearMap.lcomp _ _ f.hom ∘ₗ homLinearEquiv.toLinearMap)
参数：P : ModuleCat.{u} R；f : N ⟶ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = ofHom (homLinearEquiv.symm.toLinearMap ∘ₗ
      LinearMap.lcomp _ _ f.hom ∘ₗ homLinearEquiv.toLinearMap) :=
  rfl

end ModuleCat

