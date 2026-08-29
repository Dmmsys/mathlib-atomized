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

/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ CommRingCat.{u} where
  body: of (MvPolynomial α Int)
  map {X Y} f := ofHom (↑(rename f : _ ->ₐ[Int] _) : MvPolynomial X Int ->+* MvPolynomial Y Int)

@[simp]

中文:
定义 free
  签名: : 类型u ⥤ 交换环范畴.{u} where
  定义体: of (MvPolynomial α Int)
  map {X Y} f := ofHom (↑(rename f : _ ->ₐ[Int] _) : MvPolynomial X Int ->+* MvPolynomial Y Int)

@[simp]

Depends on / 依赖: MvPolynomial
-/
def free : Type u ⥤ CommRingCat.{u} where
  obj α := of (MvPolynomial α Int)
  map {X Y} f := ofHom (↑(rename f : _ ->ₐ[Int] _) : MvPolynomial X Int ->+* MvPolynomial Y Int)

@[simp]
/--
theorem `free_obj_coe` / 定理 `free_obj_coe`

English:
theorem free_obj_coe
  given: {α : Type u}
  statement: (free.obj α : Type u) = MvPolynomial α Int
  proof: rfl

中文:
定理 free_obj_coe
  条件: {α : 类型u}
  结论: (free.obj α : 类型u) = 多元多项式 α 整数
  证明: rfl
-/
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α Int :=
  rfl

-- This is not a `@[simp]` lemma as the left-hand side simplifies via `dsimp`.
/--
theorem `free_map_coe` / 定理 `free_map_coe`

English:
theorem free_map_coe
  given: {α β : Type u} {f : α ⟶ β}
  statement: ⇑(free.map f) = ⇑(rename f)
  proof: rfl

中文:
定理 free_map_coe
  条件: {α β : 类型u} {f : α ⟶ β}
  结论: ⇑(free.map f) = ⇑(rename f)
  证明: rfl
-/
theorem free_map_coe {α β : Type u} {f : α ⟶ β} : ⇑(free.map f) = ⇑(rename f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free ⊣ forget CommRingCat.{u}
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾(homEquiv f.hom)
invFun := fun f => ofHom homEquiv.symm f
          left_inv := fun f => congrArg ofHom (homEquiv.left_inv f.hom)
          right_inv := by cat_disch }
      homEquiv_naturality_left_symm := fun {_ _ Y}

中文:
定义 adj
  签名: : free ⊣ forget 交换环范畴.{u}
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾(homEquiv f.hom)
invFun := fun f => ofHom homEquiv.symm f
          left_inv := fun f => congrArg ofHom (homEquiv.left_inv f.hom)
          right_inv := by cat_disch }
      homEquiv_naturality_left_symm := fun {_ _ Y}

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Int.castRingHom, RingHom, RingHom.ext, castRingHom, cat_disch, f.hom, homEquiv, homEquiv.left_inv, homEquiv.symm, homEquiv_naturality_left_symm, hom_ext, invFun, left_inv, mkOfHomEquiv, right_inv
-/
def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => ↾(homEquiv f.hom)
invFun := fun f => ofHom homEquiv.symm f
          left_inv := fun f => congrArg ofHom (homEquiv.left_inv f.hom)
          right_inv := by cat_disch }
      homEquiv_naturality_left_symm := fun {_ _ Y} f g =>
hom_ext RingHom.ext fun x => eval₂_cast_comp f (Int.castRingHom Y) g x }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget CommRingCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: (forget 交换环范畴.{u}).是右伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : (forget CommRingCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

/-- `Fun(-, -)` as a functor `Type vᵒᵖ ⥤ CommRingCat ⥤ CommRingCat`. -/
@[simps]
/--
Definition of `coyoneda` / `coyoneda` 的定义

English:
definition coyoneda
  signature: : Type vᵒᵖ ⥤ CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  body: { obj R := CommRingCat.of (unop n -> R)
    map {R S} φ := CommRingCat.ofHom (RingHom.pi (φ.hom.comp <| Pi.evalRingHom _ ·)) }
  map {m n} f :=
  { app R := CommRingCat.ofHom (RingHom.pi (Pi.evalRingHom _ <| f.unop ·)) }

中文:
定义 coyoneda
  签名: : 类型vᵒᵖ ⥤ 交换环范畴.{u} ⥤ 交换环范畴.{最大值 u v} where
  定义体: { obj R := CommRingCat.of (unop n -> R)
    map {R S} φ := CommRingCat.ofHom (RingHom.pi (φ.hom.comp <| Pi.evalRingHom _ ·)) }
  map {m n} f :=
  { app R := CommRingCat.ofHom (RingHom.pi (Pi.evalRingHom _ <| f.unop ·)) }

Depends on / 依赖: CommRingCat, CommRingCat.of, CommRingCat.ofHom, Pi.evalRingHom, RingHom, RingHom.pi, evalRingHom, f.unop, hom.comp
-/
def coyoneda : Type vᵒᵖ ⥤ CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj n :=
  { obj R := CommRingCat.of (unop n -> R)
    map {R S} φ := CommRingCat.ofHom (RingHom.pi (φ.hom.comp <| Pi.evalRingHom _ ·)) }
  map {m n} f :=
  { app R := CommRingCat.ofHom (RingHom.pi (Pi.evalRingHom _ <| f.unop ·)) }

/--
Definition of `coyonedaAdj` / `coyonedaAdj` 的定义

English:
definition coyonedaAdj
  signature: (R : CommRingCat.{u})
  body: { app n := ↾fun i => CommRingCat.ofHom (Pi.evalRingHom _ i) }
  counit := { app S := (CommRingCat.ofHom (RingHom.pi fun f => f.hom)).op }

中文:
定义 coyonedaAdj
  签名: (R : 交换环范畴.{u})
  定义体: { app n := ↾fun i => CommRingCat.ofHom (Pi.evalRingHom _ i) }
  counit := { app S := (CommRingCat.ofHom (RingHom.pi fun f => f.hom)).op }

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Pi.evalRingHom, evalRingHom
-/
def coyonedaAdj (R : CommRingCat.{u}) :
    (coyoneda.flip.obj R).rightOp ⊣ yoneda.obj R where
  unit := { app n := ↾fun i => CommRingCat.ofHom (Pi.evalRingHom _ i) }
  counit := { app S := (CommRingCat.ofHom (RingHom.pi fun f => f.hom)).op }

instance (R : CommRingCat.{u}) : (yoneda.obj R).IsRightAdjoint := ⟨_, ⟨coyonedaAdj R⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `n` is a singleton, `Hom(n, -)` is the identity in `CommRingCat`. -/
@[simps!]
/--
Definition of `coyonedaUnique` / `coyonedaUnique` 的定义

English:
definition coyonedaUnique
  signature: {n : Type v} [Unique n]
  body: NatIso.ofComponents (fun X => (RingEquiv.piUnique _).toCommRingCatIso) (fun f => by ext; simp)

中文:
定义 coyonedaUnique
  签名: {n : 类型v} [唯一 n]
  定义体: NatIso.ofComponents (fun X => (RingEquiv.piUnique _).toCommRingCatIso) (fun f => by ext; simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, RingEquiv, RingEquiv.piUnique, ofComponents, piUnique, toCommRingCatIso
-/
def coyonedaUnique {n : Type v} [Unique n] : coyoneda.obj (op n) ≅ 𝟭 CommRingCat.{max u v} :=
  NatIso.ofComponents (fun X => (RingEquiv.piUnique _).toCommRingCatIso) (fun f => by ext; simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The monoid algebra functor `CommGrpCat ⥤ R-Alg` given by `G ↦ R[G]`. -/
@[simps]
/--
Definition of `monoidAlgebra` / `monoidAlgebra` 的定义

English:
definition monoidAlgebra
  signature: (R : CommRingCat.{max u v})
  body: Under.mk (CommRingCat.ofHom MonoidAlgebra.singleOneRingHom)
  map f := Under.homMk (CommRingCat.ofHom <| MonoidAlgebra.mapDomainRingHom R f.hom)
  map_comp f g := by ext : 2; apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

中文:
定义 monoidAlgebra
  签名: (R : 交换环范畴.{最大值 u v})
  定义体: Under.mk (CommRingCat.ofHom MonoidAlgebra.singleOneRingHom)
  map f := Under.homMk (CommRingCat.ofHom <| MonoidAlgebra.mapDomainRingHom R f.hom)
  map_comp f g := by ext : 2; apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, MonoidAlgebra, MonoidAlgebra.singleOneRingHom, Under.mk, singleOneRingHom
-/
def monoidAlgebra (R : CommRingCat.{max u v}) : CommMonCat.{v} ⥤ Under R where
  obj G := Under.mk (CommRingCat.ofHom MonoidAlgebra.singleOneRingHom)
  map f := Under.homMk (CommRingCat.ofHom <| MonoidAlgebra.mapDomainRingHom R f.hom)
  map_comp f g := by ext : 2; apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `monoidAlgebraAdj` / `monoidAlgebraAdj` 的定义

English:
definition monoidAlgebraAdj
  signature: (R : CommRingCat.{u})
  body: { app G := CommMonCat.ofHom (MonoidAlgebra.of R G) }
  counit :=
  { app S := Under.homMk (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom S.hom.hom
      (.id _) fun _ _ => .all _ _)) (by ext; simp [MonoidAlgebra.liftNCRingHom]),
    naturality S T f := by
      ext : 2
      apply MonoidAlgebra.rin

中文:
定义 monoidAlgebraAdj
  签名: (R : 交换环范畴.{u})
  定义体: { app G := CommMonCat.ofHom (MonoidAlgebra.of R G) }
  counit :=
  { app S := Under.homMk (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom S.hom.hom
      (.id _) fun _ _ => .all _ _)) (by ext; simp [MonoidAlgebra.liftNCRingHom]),
    naturality S T f := by
      ext : 2
      apply MonoidAlgebra.rin

Depends on / 依赖: CommMonCat, CommMonCat.ofHom, MonoidAlgebra, MonoidAlgebra.of
-/
def monoidAlgebraAdj (R : CommRingCat.{u}) :
    monoidAlgebra R ⊣ Under.forget R ⋙ forget₂ _ _ where
  unit := { app G := CommMonCat.ofHom (MonoidAlgebra.of R G) }
  counit :=
  { app S := Under.homMk (CommRingCat.ofHom (MonoidAlgebra.liftNCRingHom S.hom.hom
      (.id _) fun _ _ => .all _ _)) (by ext; simp [MonoidAlgebra.liftNCRingHom]),
    naturality S T f := by
      ext : 2
      apply MonoidAlgebra.ringHom_ext <;>
        intro <;> simp [MonoidAlgebra.liftNCRingHom, ← Under.w f, -Under.w] }
  left_triangle_components G := by
    ext : 2
    apply MonoidAlgebra.ringHom_ext <;> intro <;> simp [MonoidAlgebra.liftNCRingHom]
  right_triangle_components S := by dsimp; ext; simp [MonoidAlgebra.liftNCRingHom]

/--
Definition of `forget₂Adj` / `forget₂Adj` 的定义

English:
definition forget₂Adj
  signature: {R : CommRingCat.{u}} (hR : Limits.IsInitial R)
  body: (monoidAlgebraAdj R).comp (Under.equivalenceOfIsInitial hR).toAdjunction

中文:
定义 forget₂Adj
  签名: {R : 交换环范畴.{u}} (hR : Limits.IsInitial R)
  定义体: (monoidAlgebraAdj R).comp (Under.equivalenceOfIsInitial hR).toAdjunction

Depends on / 依赖: Under.equivalenceOfIsInitial, equivalenceOfIsInitial, monoidAlgebraAdj, toAdjunction
-/
def forget₂Adj {R : CommRingCat.{u}} (hR : Limits.IsInitial R) :
    monoidAlgebra R ⋙ Under.forget R ⊣ forget₂ _ _ :=
  (monoidAlgebraAdj R).comp (Under.equivalenceOfIsInitial hR).toAdjunction

instance (R : CommRingCat) : (monoidAlgebra.{u, u} R).IsLeftAdjoint :=
  ⟨_, ⟨CommRingCat.monoidAlgebraAdj R⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ CommRingCat CommMonCat).IsRightAdjoint
  body: ⟨_, ⟨CommRingCat.forget₂Adj Limits.initialIsInitial⟩⟩

中文:
实例 :
  签名: (forget₂ 交换环范畴 交换幺半群范畴).是右伴随
  定义体: ⟨_, ⟨CommRingCat.forget₂Adj Limits.initialIsInitial⟩⟩

Depends on / 依赖: CommRingCat, CommRingCat.forget, Limits, Limits.initialIsInitial, initialIsInitial
-/
instance : (forget₂ CommRingCat CommMonCat).IsRightAdjoint :=
  ⟨_, ⟨CommRingCat.forget₂Adj Limits.initialIsInitial⟩⟩

end CommRingCat
