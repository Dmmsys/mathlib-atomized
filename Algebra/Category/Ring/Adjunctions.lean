/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Adjunctions in `CommRingCat`

## Main results
- `CommRingCat.adj`: `σ ↦ ℤ[σ]` is left adjoint to the forgetful functor `CommRingCat ⥤ Type`.
- `CommRingCat.coyonedaAdj`: `Fun(-, R)` is left adjoint to `Hom_{CRing}(R, -)`.
- `CommRingCat.monoidAlgebraAdj`: `G ↦ R[G]` as `CommGrpCat ⥤ R-Alg` is left adjoint to `S ↦ Sˣ`.
- `CommRingCat.unitsAdj`: `G ↦ ℤ[G]` is left adjoint to `S ↦ Sˣ`.

-/

@[expose] public section

noncomputable section

universe v u

open MvPolynomial Opposite CategoryTheory

namespace CommRingCat

/-- The free functor `Type u ⥤ CommRingCat` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
/-
**CommRingCat.free** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：free : Type u ⥤ CommRingCat.{u} where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor `Type u ⥤ CommRingCat` sending a type `X` to the multivariable 
(commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRingCat.{u} where
  obj α := of (MvPolynomial α ℤ)
  map {X Y} f := ofHom (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)

@[simp]
/-
**CommRingCat.free_obj_coe** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α Int
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl

-- This is not a `@[simp]` lemma as the left-hand side simplifies via `dsimp`.
/-
**CommRingCat.free_map_coe** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：free_map_coe {α β : Type u} {f : α ⟶ β} : ⇑(free.map f) = ⇑(rename f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem free_map_coe {α β : Type u} {f : α ⟶ β} : ⇑(free.map f) = ⇑(rename f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The free-forgetful adjunction for commutative rings. -/
/-
**CommRingCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：adj : free ⊣ forget CommRingCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦
        { toFun := fun f ↦ ↾(homEquiv f.hom)
          invFun := fun f ↦ ofHom <| homEquiv.symm f
          left_inv := fun f ↦ congrArg ofHom (homEquiv.left_inv f.hom)
          right_inv := by cat_disch }
      homEquiv_naturality_left_symm := fun {_ _ Y} f g =>
        hom_ext <| RingHom.ext fun x ↦ eval₂_cast_comp f (Int.castRingHom Y) g x }
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget CommRingCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- `Fun(-, -)` as a functor `Type vᵒᵖ ⥤ CommRingCat ⥤ CommRingCat`. -/
@[simps]
/-
**CommRingCat.coyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：coyoneda : Type vᵒᵖ ⥤ CommRingCat.{u} ⥤ CommRingCat.{max u v} where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fun(-, -)` as a functor `Type vᵒᵖ ⥤ CommRingCat ⥤ CommRingCat`.
-/
def coyoneda : Type vᵒᵖ ⥤ CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj n :=
  { obj R := CommRingCat.of (unop n → R)
    map {R S} φ := CommRingCat.ofHom (RingHom.pi (φ.hom.comp <| Pi.evalRingHom _ ·)) }
  map {m n} f :=
  { app R := CommRingCat.ofHom (RingHom.pi (Pi.evalRingHom _ <| f.unop ·)) }

/-- The adjunction `Hom_{CRing}(Fun(n, R), S) ≃ Fun(n, Hom_{CRing}(R, S))`. -/
/-
**CommRingCat.coyonedaAdj** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：coyonedaAdj (R : CommRingCat.{u}) : (coyoneda.flip.obj R).rightOp ⊣ yoneda
.obj R where unit
参数：R : CommRingCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `Hom_{CRing}(Fun(n, R), S) ≃ Fun(n, Hom_{CRing}(R, S))`.
-/
def coyonedaAdj (R : CommRingCat.{u}) :
    (coyoneda.flip.obj R).rightOp ⊣ yoneda.obj R where
  unit := { app n := ↾fun i ↦ CommRingCat.ofHom (Pi.evalRingHom _ i) }
  counit := { app S := (CommRingCat.ofHom (RingHom.pi fun f ↦ f.hom)).op }
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : CommRingCat.{u}) : (yoneda.obj R).IsRightAdjoint := ⟨_, ⟨coyonedaAdj R⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `n` is a singleton, `Hom(n, -)` is the identity in `CommRingCat`. -/
@[simps!]
/-
**CommRingCat.coyonedaUnique** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：coyonedaUnique {n : Type v} [Unique n] : coyoneda.obj (op n) ≅ 𝟭 CommRingC
at.{max u v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `n` is a singleton, `Hom(n, -)` is the identity in `CommRingCat`.
-/
def coyonedaUnique {n : Type v} [Unique n] : coyoneda.obj (op n) ≅ 𝟭 CommRingCat.{max u v} :=
  NatIso.ofComponents (fun X ↦ (RingEquiv.piUnique _).toCommRingCatIso) (fun f ↦ by ext; simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The monoid algebra functor `CommGrpCat ⥤ R-Alg` given by `G ↦ R[G]`. -/
@[simps]
/-
**CommRingCat.monoidAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：monoidAlgebra (R : CommRingCat.{max u v}) : CommMonCat.{v} ⥤ Under R where
 obj G
参数：R : CommRingCat.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid algebra functor `CommGrpCat ⥤ R-Alg` given by `G ↦ R[G]`.
-/
def monoidAlgebra (R : CommRingCat.{max u v}) : CommMonCat.{v} ⥤ Under R where
  obj G := Under.mk (CommRingCat.ofHom MonoidAlgebra.singleOneRingHom)
  map f := Under.homMk (CommRingCat.ofHom <| MonoidAlgebra.mapDomainRingHom R f.hom)
  map_comp f g := by ext : 2; apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction `G ↦ R[G]` and `S ↦ Sˣ` between `CommGrpCat` and `R-Alg`. -/
/-
**CommRingCat.monoidAlgebraAdj** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：monoidAlgebraAdj (R : CommRingCat.{u}) : monoidAlgebra R ⊣ Under.forget R 
⋙ forget₂ _ _ where unit
参数：R : CommRingCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `G ↦ R[G]` and `S ↦ Sˣ` between `CommGrpCat` and `R-Alg`.
-/
def monoidAlgebraAdj (R : CommRingCat.{u}) :
    monoidAlgebra R ⊣ Under.forget R ⋙ forget₂ _ _ where
  unit := { app G := CommMonCat.ofHom (MonoidAlgebra.of R G) }
  counit :=
  { app S := Under.homMk (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom S.hom.hom
      (.id _) fun _ _ ↦ .all _ _)) (by ext; simp [MonoidAlgebra.liftNCRingHom]),
    naturality S T f := by
      ext : 2
      apply MonoidAlgebra.ringHom_ext <;>
        intro <;> simp [MonoidAlgebra.liftNCRingHom, ← Under.w f, -Under.w] }
  left_triangle_components G := by
    ext : 2
    apply MonoidAlgebra.ringHom_ext <;> intro <;> simp [MonoidAlgebra.liftNCRingHom]
  right_triangle_components S := by dsimp; ext; simp [MonoidAlgebra.liftNCRingHom]

/-- The adjunction `G ↦ ℤ[G]` and `R ↦ Rˣ` between `CommGrpCat` and `CommRing`. -/
/-
**CommRingCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `G ↦ ℤ[G]` and `R ↦ Rˣ` between `CommGrpCat` and `CommRing`.
-/
def forget₂Adj {R : CommRingCat.{u}} (hR : Limits.IsInitial R) :
    monoidAlgebra R ⋙ Under.forget R ⊣ forget₂ _ _ :=
  (monoidAlgebraAdj R).comp (Under.equivalenceOfIsInitial hR).toAdjunction
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : CommRingCat) : (monoidAlgebra.{u, u} R).IsLeftAdjoint :=
  ⟨_, ⟨CommRingCat.monoidAlgebraAdj R⟩⟩
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ CommRingCat CommMonCat).IsRightAdjoint :=
  ⟨_, ⟨CommRingCat.forget₂Adj Limits.initialIsInitial⟩⟩

end CommRingCat

