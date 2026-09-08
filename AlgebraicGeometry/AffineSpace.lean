/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine space

## Main definitions

- `AlgebraicGeometry.AffineSpace`: `𝔸(n; S)` is the affine `n`-space over `S`.
- `AlgebraicGeometry.AffineSpace.coord`: The standard coordinate functions on the affine space.
- `AlgebraicGeometry.AffineSpace.homOfVector`:
  The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions.
- `AlgebraicGeometry.AffineSpace.homOverEquiv`:
  `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections.
- `AlgebraicGeometry.AffineSpace.SpecIso`: `𝔸(n; Spec R) ≅ Spec R[n]`

-/

@[expose] public section

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe u

variable (n : Type u) (S : Scheme.{u})

local notation3 "ℤ[" n "]" => CommRingCat.of (MvPolynomial n (ULift ℤ))

/-- `𝔸(n; S)` is the affine `n`-space over `S`.
Note that `n : Type u` is an arbitrary index type (e.g. `ULift.{u} (Fin m)`). -/
/-
**AlgebraicGeometry.AffineSpace** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：AffineSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u}
参数：n : Type u；S : Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme

--- 原说明 ---
`𝔸(n; S)` is the affine `n`-space over `S`.
Note that `n : Type u` is an arbitrary index type (e.g. `ULift.{u} (Fin m)`).
-/
def AffineSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Spec ℤ[n]))

namespace AffineSpace

/-- `𝔸(n; S)` is the affine `n`-space over `S`. -/
scoped[AlgebraicGeometry] notation "𝔸(" n "; " S ")" => AffineSpace n S

variable {n} in
/-
**AlgebraicGeometry.AffineSpace.of_mvPolynomial_int_ext** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：of_mvPolynomial_int_ext {R} {f g : Int[n] ⟶ R} (h : forall i, f (.X i) = g
 (.X i)) : f = g
参数：h : forall i, f (.X i) = g (.X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma of_mvPolynomial_int_ext {R} {f g : ℤ[n] ⟶ R} (h : ∀ i, f (.X i) = g (.X i)) : f = g := by
  suffices f.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
      g.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    ext x
    · obtain ⟨x⟩ := x
      simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (C x)
    · simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (X x)
  ext1
  · exact RingHom.ext_int _ _
  · simpa using! h _


@[simps -isSimp]
/-
**AlgebraicGeometry.AffineSpace.over** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.AffineSpace`。
形式化陈述：over : 𝔸(n; S).CanonicallyOver S where hom
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
-/
instance over : 𝔸(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the affine `n`-space over `S` to the integral model `Spec ℤ[n]`. -/
/-
**AlgebraicGeometry.AffineSpace.toSpecMvPoly** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.AffineSpace`。
形式化陈述：toSpecMvPoly : 𝔸(n; S) ⟶ Spec Int[n]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme

--- 原说明 ---
The map from the affine `n`-space over `S` to the integral model `Spec ℤ[n]`.
-/
def toSpecMvPoly : 𝔸(n; S) ⟶ Spec ℤ[n] := pullback.snd _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Morphisms into `Spec ℤ[n]` are equivalent the choice of `n` global sections.
Use `homOverEquiv` instead.
-/
@[simps]
/-
**AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.AffineSpace`。
形式化陈述：toSpecMvPolyIntEquiv {X : Scheme.{u}} : (X ⟶ Spec Int[n]) ≃ (n -> Γ(X, ⊤))
 where toFun f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms into `Spec ℤ[n]` are equivalent the choice of `n` global sections.
Use `homOverEquiv` instead.
-/
def toSpecMvPolyIntEquiv {X : Scheme.{u}} : (X ⟶ Spec ℤ[n]) ≃ (n → Γ(X, ⊤)) where
  toFun f i := f.appTop ((Scheme.ΓSpecIso ℤ[n]).inv (.X i))
  invFun v := X.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((algebraMap ℤ _).comp ULift.ringEquiv.toRingHom) v))
  left_inv f := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
    dsimp
    simp only [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    apply of_mvPolynomial_int_ext
    intro i
    rw [ConcreteCategory.hom_ofHom, coe_eval₂Hom, eval₂_X]
    rfl
  right_inv v := by ext; simp
/-
**AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：toSpecMvPolyIntEquiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec Int[n])
 (i) : toSpecMvPolyIntEquiv n (f ≫ g) i = f.appTop (toSpecMvPolyIntEquiv n g i)
参数：f : X ⟶ Y；g : Y ⟶ Spec Int[n]；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecMvPolyIntEquiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec ℤ[n]) (i) :
    toSpecMvPolyIntEquiv n (f ≫ g) i = f.appTop (toSpecMvPolyIntEquiv n g i) := rfl

variable {n} in
/-- The standard coordinates of `𝔸(n; S)`. -/
/-
**AlgebraicGeometry.AffineSpace.coord** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.AffineSpace`。
形式化陈述：coord (i : n) : Γ(𝔸(n; S), ⊤)
参数：i : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard coordinates of `𝔸(n; S)`.
-/
def coord (i : n) : Γ(𝔸(n; S), ⊤) := toSpecMvPolyIntEquiv _ (toSpecMvPoly n S) i

section homOfVector

variable {n S}

/-- The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions. -/
/-
**AlgebraicGeometry.AffineSpace.homOfVector** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.AffineSpace`。
形式化陈述：homOfVector {X : Scheme.{u}} (f : X ⟶ S) (v : n -> Γ(X, ⊤)) : X ⟶ 𝔸(n; S)
参数：f : X ⟶ S；v : n -> Γ(X, ⊤)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate fun
ctions.
-/
def homOfVector {X : Scheme.{u}} (f : X ⟶ S) (v : n → Γ(X, ⊤)) : X ⟶ 𝔸(n; S) :=
  pullback.lift f ((toSpecMvPolyIntEquiv n).symm v) (by simp)

variable {X : Scheme.{u}} (f : X ⟶ S) (v : n → Γ(X, ⊤))

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.AffineSpace.homOfVector_over** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.AffineSpace`。
形式化陈述：homOfVector_over : homOfVector f v ≫ 𝔸(n; S) ↘ S = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma homOfVector_over : homOfVector f v ≫ 𝔸(n; S) ↘ S = f :=
  pullback.lift_fst _ _ _

@[reassoc]
/-
**AlgebraicGeometry.AffineSpace.homOfVector_toSpecMvPoly** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：homOfVector_toSpecMvPoly : homOfVector f v ≫ toSpecMvPoly n S = (toSpecMvP
olyIntEquiv n).symm v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma homOfVector_toSpecMvPoly :
    homOfVector f v ≫ toSpecMvPoly n S = (toSpecMvPolyIntEquiv n).symm v :=
  pullback.lift_snd _ _ _

@[simp]
/-
**AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：homOfVector_appTop_coord (i) : (homOfVector f v).appTop (coord S i) = v i
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.AffineSpace.coord.eq_1`：∀ {n : Type u} (S : AlgebraicG
eometry.Scheme) (i : n),   AlgebraicGeometry.AffineSpace.coord S i =     (Algebr
aicGeometry.AffineSpace.toSpec…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp`：toSpecMvPolyInt
Equiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec Int[n]) (i) : toSpecMvPolyIn
tEquiv n (f ≫ g) i = f.appTop (toSpecMvPolyIn…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `AlgebraicGeometry.AffineSpace.homOfVector_toSpecMvPoly`：homOfVector_toSp
ecMvPoly : homOfVector f v ≫ toSpecMvPoly n S = (toSpecMvPolyIntEquiv n).symm v
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma homOfVector_appTop_coord (i) :
    (homOfVector f v).appTop (coord S i) = v i := by
  rw [coord, ← toSpecMvPolyIntEquiv_comp, homOfVector_toSpecMvPoly,
    Equiv.apply_symm_apply]

@[ext 1100]
/-
**AlgebraicGeometry.AffineSpace.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.AffineSpace`。
形式化陈述：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ :
 forall i, f.appTop (coord S i) = g.appTop (coord S i)) : f = g
参数：n; S；h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S；h₂ : forall i, f.appTop (coord S 
i) = g.appTop (coord S i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp`：toSpecMvPolyInt
Equiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec Int[n]) (i) : toSpecMvPolyIn
tEquiv n (f ≫ g) i = f.appTop (toSpecMvPolyIn…
-/
lemma hom_ext {f g : X ⟶ 𝔸(n; S)}
    (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S)
    (h₂ : ∀ i, f.appTop (coord S i) = g.appTop (coord S i)) : f = g := by
  apply pullback.hom_ext h₁
  change f ≫ toSpecMvPoly _ _ = g ≫ toSpecMvPoly _ _
  apply (toSpecMvPolyIntEquiv n).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp, toSpecMvPolyIntEquiv_comp]
  exact h₂ i

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.AffineSpace.comp_homOfVector** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.AffineSpace`。
形式化陈述：comp_homOfVector {X Y : Scheme} (v : n -> Γ(Y, ⊤)) (f : X ⟶ Y) (g : Y ⟶ S)
 : f ≫ homOfVector g v = homOfVector (f ≫ g) (f.appTop ∘ v)
参数：v : n -> Γ(Y, ⊤)；f : X ⟶ Y；g : Y ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.AffineSpace.homOfVector_over`：homOfVector_over : homOf
Vector f v ≫ 𝔸(n; S) ↘ S = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord`：homOfVector_appT
op_coord (i) : (homOfVector f v).appTop (coord S i) = v i
-/
lemma comp_homOfVector {X Y : Scheme} (v : n → Γ(Y, ⊤)) (f : X ⟶ Y) (g : Y ⟶ S) :
    f ≫ homOfVector g v = homOfVector (f ≫ g) (f.appTop ∘ v) := by
  ext1 <;> simp

end homOfVector

variable {n}

/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} [X.Over S] (v : n → Γ(X, ⊤)) :
    (homOfVector (X ↘ S) v).IsOver S where

/-- `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections. -/
@[simps]
/-
**AlgebraicGeometry.AffineSpace.homOverEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.AffineSpace`。
形式化陈述：homOverEquiv {X : Scheme.{u}} [X.Over S] : { f : X ⟶ 𝔸(n; S) // f.IsOver S
 } ≃ (n -> Γ(X, ⊤)) where toFun f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sec
tions.
-/
def homOverEquiv {X : Scheme.{u}} [X.Over S] :
    { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤)) where
  toFun f i := f.1.appTop (coord S i)
  invFun v := ⟨homOfVector (X ↘ S) v, inferInstance⟩
  left_inv f := by
    ext : 2
    · simp [f.2.1]
    · rw [homOfVector_appTop_coord]
  right_inv v := by ext i; simp [-TopologicalSpace.Opens.map_top, homOfVector_appTop_coord]

set_option backward.isDefEq.respectTransparency.types false in
variable (n) in
/--
The affine space over an affine base is isomorphic to the spectrum of the polynomial ring.
Also see `AffineSpace.SpecIso`.
-/
@[simps -isSimp hom inv]
/-
**AlgebraicGeometry.AffineSpace.isoOfIsAffine** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.AffineSpace`。
形式化陈述：isoOfIsAffine [IsAffine S] : 𝔸(n; S) ≅ Spec .of MvPolynomial n Γ(S, ⊤) whe
re hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine space over an affine base is isomorphic to the spectrum of the polyno
mial ring.
Also see `AffineSpace.SpecIso`.
-/
def isoOfIsAffine [IsAffine S] :
    𝔸(n; S) ≅ Spec <| .of <| MvPolynomial n Γ(S, ⊤) where
      hom := 𝔸(n; S).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)))
      inv := homOfVector (Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv)
        ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(S, ⊤)))).inv ∘ MvPolynomial.X)
      hom_inv_id := by
        ext1
        · simp only [Category.assoc, homOfVector_over, Category.id_comp]
          rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, eval₂Hom_comp_C,
            CommRingCat.ofHom_hom, ← Scheme.toSpecΓ_naturality_assoc]
          simp [Scheme.isoSpec]
        · simp
      inv_hom_id := by
        apply ext_of_isAffine
        simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
          TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, Scheme.toSpecΓ_appTop,
          Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.Hom.id_app, ← Iso.eq_inv_comp,
          Category.comp_id]
        ext : 1
        apply ringHom_ext'
        · change _ = (CommRingCat.ofHom C ≫ _).hom
          rw [CommRingCat.hom_comp, RingHom.comp_assoc, CommRingCat.hom_ofHom, eval₂Hom_comp_C,
            ← CommRingCat.hom_comp, ← CommRingCat.hom_ext_iff,
            ← cancel_mono (Scheme.ΓSpecIso _).hom]
          rw [← Scheme.Hom.comp_appTop, homOfVector_over, Scheme.Hom.comp_appTop]
          simp only [Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.of_carrier,
            ← Scheme.toSpecΓ_appTop]
          rw [← Scheme.Hom.comp_appTop_assoc, Scheme.isoSpec, asIso_inv, IsIso.hom_inv_id]
          simp
        · intro i
          rw [CommRingCat.comp_apply, ConcreteCategory.hom_ofHom, coe_eval₂Hom]
          simp only [eval₂_X]
          exact homOfVector_appTop_coord _ _ _

@[simp]
/-
**AlgebraicGeometry.AffineSpace.isoOfIsAffine_hom_appTop** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：isoOfIsAffine_hom_appTop [IsAffine S] : (isoOfIsAffine n S).hom.appTop = (
Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom 
(coord S))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.AffineSpace.isoOfIsAffine_hom`：∀ (n : Type u) (S : Alg
ebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsAffine S],   (AlgebraicGeomet
ry.AffineSpace.isoOfIsAffine n S).hom…
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_appTop`：∀ (X : AlgebraicGeometry.Scheme
),   AlgebraicGeometry.Scheme.Hom.appTop X.toSpecΓ =     (AlgebraicGeometry.Sche
me.ΓSpecIso (X.presheaf.obj (…
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`：ΓSpecIso_naturality {R S :
 CommRingCat.{u}} (f : R ⟶ S) : (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecI
so R).hom ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isoOfIsAffine_hom_appTop [IsAffine S] :
    (isoOfIsAffine n S).hom.appTop =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom
        (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)) := by
  simp [isoOfIsAffine_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_appTop_coord** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：isoOfIsAffine_inv_appTop_coord [IsAffine S] (i) : (isoOfIsAffine n S).inv.
appTop (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i)
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord`：homOfVector_appT
op_coord (i) : (homOfVector f v).appTop (coord S i) = v i
-/
lemma isoOfIsAffine_inv_appTop_coord [IsAffine S] (i) :
    (isoOfIsAffine n S).inv.appTop (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) :=
  homOfVector_appTop_coord _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_over** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.AffineSpace`。
形式化陈述：isoOfIsAffine_inv_over [IsAffine S] : (isoOfIsAffine n S).inv ≫ 𝔸(n; S) ↘ 
S = Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isoOfIsAffine_inv_over [IsAffine S] :
    (isoOfIsAffine n S).inv ≫ 𝔸(n; S) ↘ S = Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv :=
  pullback.lift_fst _ _ _
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAffine S] : IsAffine 𝔸(n; S) := .of_isIso (isoOfIsAffine n S).hom

variable (n) in
/-- The affine space over an affine base is isomorphic to the spectrum of the polynomial ring. -/
/-
**AlgebraicGeometry.AffineSpace.SpecIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.AffineSpace`。
形式化陈述：SpecIso (R : CommRingCat.{u}) : 𝔸(n; Spec R) ≅ Spec .of MvPolynomial n R
参数：R : CommRingCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine space over an affine base is isomorphic to the spectrum of the polyno
mial ring.
-/
def SpecIso (R : CommRingCat.{u}) :
    𝔸(n; Spec R) ≅ Spec <| .of <| MvPolynomial n R :=
  isoOfIsAffine _ _ ≪≫ Scheme.Spec.mapIso (MvPolynomial.mapEquiv _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).toCommRingCatIso.op

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.AffineSpace.SpecIso_hom_appTop** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.AffineSpace`。
形式化陈述：SpecIso_hom_appTop (R : CommRingCat.{u}) : (SpecIso n R).hom.appTop = (Sch
eme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (eval₂Hom ((Scheme.ΓSpecIso _).inv ≫ (𝔸(
n; Spec R) ↘ Spec R).appTop).hom (coord (Spec R)))
参数：R : CommRingCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `RingEquiv.toCommRingCatIso_hom`：∀ {R S : Type u} [inst : CommRing R] [in
st_1 : CommRing S] (e : R ≃+* S), e.toCommRingCatIso.hom = CommRingCat.ofHom ↑e
· 使用引理 `AlgebraicGeometry.AffineSpace.isoOfIsAffine_hom_appTop`：isoOfIsAffine_ho
m_appTop [IsAffine S] : (isoOfIsAffine n S).hom.appTop = (Scheme.ΓSpecIso _).hom
 ≫ CommRingCat.ofHom (eval₂Hom ((𝔸(n; S) ↘ S…
· 使用定理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality_assoc`：∀ {R S : CommRingCat
} (f : R ⟶ S) {Z : CommRingCat} (h : S ⟶ Z),   CategoryTheory.CategoryStruct.com
p (AlgebraicGeometry.Scheme.Hom.appTop (…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MvPolynomial.eval₂_map`：eval₂_map [CommSemiring S₂] (f : R ->+* S₁) (g :
 σ -> S₂) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : eval₂ φ g (map f p) = eval₂ 
(φ.comp f) g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SpecIso_hom_appTop (R : CommRingCat.{u}) :
    (SpecIso n R).hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (eval₂Hom ((Scheme.ΓSpecIso _).inv ≫
        (𝔸(n; Spec R) ↘ Spec R).appTop).hom (coord (Spec R))) := by
  ext i
  simp [SpecIso]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：SpecIso_inv_appTop_coord (R : CommRingCat.{u}) (i) : (SpecIso n R).inv.app
Top (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i)
参数：R : CommRingCat.{u}；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用引理 `AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_appTop_coord`：isoOfIsAff
ine_inv_appTop_coord [IsAffine S] (i) : (isoOfIsAffine n S).inv.appTop (coord _ 
i) = (Scheme.ΓSpecIso (.of _)).inv (.X i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`：ΓSpecIso_inv_naturalit
y {R S : CommRingCat.{u}} (f : R ⟶ S) : f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv 
≫ (Spec.map f).appTop
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
-/
lemma SpecIso_inv_appTop_coord (R : CommRingCat.{u}) (i) :
    (SpecIso n R).inv.appTop (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  rw [isoOfIsAffine_inv_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
  congr 1
  exact map_X _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.AffineSpace.SpecIso_inv_over** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.AffineSpace`。
形式化陈述：SpecIso_inv_over (R : CommRingCat.{u}) : (SpecIso n R).inv ≫ 𝔸(n; Spec R) 
↘ Spec R = Spec.map (CommRingCat.ofHom C)
参数：R : CommRingCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.op_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.inv = α.inv.op
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_over`：isoOfIsAffine_inv_
over [IsAffine S] : (isoOfIsAffine n S).inv ≫ 𝔸(n; S) ↘ S = Spec.map (CommRingCa
t.ofHom C) ≫ S.isoSpec.inv
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_Spec_inv`：∀ (R : CommRingCat),   (Algeb
raicGeometry.Spec R).isoSpec.inv = AlgebraicGeometry.Spec.map (AlgebraicGeometry
.Scheme.ΓSpecIso R).inv
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
-/
lemma SpecIso_inv_over (R : CommRingCat.{u}) :
    (SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R = Spec.map (CommRingCat.ofHom C) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc, isoOfIsAffine_inv_over, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  congr 1
  rw [Iso.inv_comp_eq]
  ext : 2
  exact map_C _ _

section functorial

variable (n) in
/-- `𝔸(n; S)` is functorial w.r.t. `S`. -/
/-
**AlgebraicGeometry.AffineSpace.map** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.AffineSpace`。
形式化陈述：map {S T : Scheme.{u}} (f : S ⟶ T) : 𝔸(n; S) ⟶ 𝔸(n; T)
参数：f : S ⟶ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`𝔸(n; S)` is functorial w.r.t. `S`.
-/
def map {S T : Scheme.{u}} (f : S ⟶ T) : 𝔸(n; S) ⟶ 𝔸(n; T) :=
  homOfVector (𝔸(n; S) ↘ S ≫ f) (coord S)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.AffineSpace.map_over** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.AffineSpace`。
形式化陈述：map_over {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) 
↘ S ≫ f
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

@[simp]
/-
**AlgebraicGeometry.AffineSpace.map_appTop_coord** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.AffineSpace`。
形式化陈述：map_appTop_coord {S T : Scheme.{u}} (f : S ⟶ T) (i) : (map n f).appTop (co
ord T i) = coord S i
参数：f : S ⟶ T；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord`：homOfVector_appT
op_coord (i) : (homOfVector f v).appTop (coord S i) = v i
-/
lemma map_appTop_coord {S T : Scheme.{u}} (f : S ⟶ T) (i) :
    (map n f).appTop (coord T i) = coord S i :=
  homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.AffineSpace.map_toSpecMvPoly** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.AffineSpace`。
形式化陈述：map_toSpecMvPoly {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ toSpecMvPoly n
 T = toSpecMvPoly n S
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp`：toSpecMvPolyInt
Equiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec Int[n]) (i) : toSpecMvPolyIn
tEquiv n (f ≫ g) i = f.appTop (toSpecMvPolyIn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineSpace.coord.eq_1`：∀ {n : Type u} (S : AlgebraicG
eometry.Scheme) (i : n),   AlgebraicGeometry.AffineSpace.coord S i =     (Algebr
aicGeometry.AffineSpace.toSpec…
· 使用引理 `AlgebraicGeometry.AffineSpace.map_appTop_coord`：map_appTop_coord {S T : 
Scheme.{u}} (f : S ⟶ T) (i) : (map n f).appTop (coord T i) = coord S i
-/
lemma map_toSpecMvPoly {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toSpecMvPoly n T = toSpecMvPoly n S := by
  apply (toSpecMvPolyIntEquiv _).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp, ← coord, map_appTop_coord, coord]

@[simp]
/-
**AlgebraicGeometry.AffineSpace.map_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeome
try.AffineSpace`。
形式化陈述：map_id : map n (𝟙 S) = 𝟙 𝔸(n; S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.AffineSpace.map_over`：map_over {S T : Scheme.{u}} (f :
 S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.instHomIsOverId`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.HomIsOver…
· 使用引理 `AlgebraicGeometry.AffineSpace.map_appTop_coord`：map_appTop_coord {S T : 
Scheme.{u}} (f : S ⟶ T) (i) : (map n f).appTop (coord T i) = coord S i
-/
lemma map_id : map n (𝟙 S) = 𝟙 𝔸(n; S) := by
  ext1 <;> simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc, simp]
/-
**AlgebraicGeometry.AffineSpace.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.AffineSpace`。
形式化陈述：map_comp {S S' S'' : Scheme} (f : S ⟶ S') (g : S' ⟶ S'') : map n (f ≫ g) =
 map n f ≫ map n g
参数：f : S ⟶ S'；g : S' ⟶ S''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.AffineSpace.map_over`：map_over {S T : Scheme.{u}} (f :
 S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.AffineSpace.map_over_assoc`：∀ {n : Type u} {S T : Alge
braicGeometry.Scheme} (f : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : T ⟶ Z),   
CategoryTheory.CategoryStruct.comp…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.AffineSpace.map_appTop_coord`：map_appTop_coord {S T : 
Scheme.{u}} (f : S ⟶ T) (i) : (map n f).appTop (coord T i) = coord S i
-/
lemma map_comp {S S' S'' : Scheme} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1
  · simp
  · simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.map_SpecMap** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.AffineSpace`。
形式化陈述：map_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) : map n (Spec.map φ) = (Sp
ecIso n S).hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.map φ.hom)) ≫ (SpecIs
o n R).inv
参数：φ : R ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.AffineSpace.map_over`：map_over {S T : Scheme.{u}} (f :
 S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
· 使用定理 `AlgebraicGeometry.AffineSpace.SpecIso_inv_over_assoc`：∀ {n : Type u} (R 
: CommRingCat) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.CategoryStruct.comp (Al…
· 使用引理 `AlgebraicGeometry.AffineSpace.SpecIso_inv_over`：SpecIso_inv_over (R : Co
mmRingCat.{u}) : (SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R = Spec.map (CommRingC
at.ofHom C)
· 使用定理 `MvPolynomial.map_comp_C`：map_comp_C (f : R ->+* S) : (map f).comp (C : R
 ->+* MvPolynomial σ R) = C.comp f
· 使用引理 `CommRingCat.ofHom_comp`：ofHom_comp {R S T : Type u} [CommRing R] [CommRi
ng S] [CommRing T] (f : R ->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ 
ofHom g
· 使用引理 `CommRingCat.ofHom_hom`：ofHom_hom {R S : CommRingCat} (f : R ⟶ S) : ofHom
 (Hom.hom f) = f
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用引理 `AlgebraicGeometry.AffineSpace.map_appTop_coord`：map_appTop_coord {S T : 
Scheme.{u}} (f : S ⟶ T) (i) : (map n f).appTop (coord T i) = coord S i
· 使用引理 `AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord`：SpecIso_inv_appT
op_coord (R : CommRingCat.{u}) (i) : (SpecIso n R).inv.appTop (coord _ i) = (Sch
eme.ΓSpecIso (.of _)).inv (.X i)
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`：ΓSpecIso_inv_naturalit
y {R S : CommRingCat.{u}} (f : R ⟶ S) : f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv 
≫ (Spec.map f).appTop
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
-/
lemma map_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    map n (Spec.map φ) =
      (SpecIso n S).hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.map φ.hom)) ≫
        (SpecIso n R).inv := by
  rw [← Iso.inv_comp_eq]
  ext1
  · simp only [map_over, Category.assoc, SpecIso_inv_over, SpecIso_inv_over_assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [map_comp_C, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]
  · simp only [TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
    conv_lhs => enter [2]; tactic => exact map_appTop_coord _ _
    conv_rhs => enter [2]; tactic => exact SpecIso_inv_appTop_coord _ _
    rw [SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply, ConcreteCategory.hom_ofHom, map_X]

set_option backward.defeqAttrib.useBackward true in
/-- The map between affine spaces over affine bases is
isomorphic to the natural map between polynomial rings. -/
/-
**AlgebraicGeometry.AffineSpace.mapSpecMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.AffineSpace`。
形式化陈述：mapSpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) : Arrow.mk (map n (Spec.map
 φ)) ≅ Arrow.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ
参数：φ : R ⟶ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between affine spaces over affine bases is
isomorphic to the natural map between polynomial rings.
-/
def mapSpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Arrow.mk (map n (Spec.map φ)) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := n) φ.hom))) :=
  Arrow.isoMk (SpecIso n S) (SpecIso n R) (by have := (SpecIso n R).inv_hom_id; simp [map_SpecMap])

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.AffineSpace.isPullback_map** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.AffineSpace`。
形式化陈述：isPullback_map {S T : Scheme.{u}} (f : S ⟶ T) : IsPullback (map n f) (𝔸(n;
 S) ↘ S) (𝔸(n; T) ↘ T) f
参数：f : S ⟶ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsPullback.paste_horiz_iff`：paste_horiz_iff {X₁₁ X₁₂ X₁₃ 
X₂₁ X₂₂ X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂
₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用引理 `AlgebraicGeometry.AffineSpace.map_over`：map_over {S T : Scheme.{u}} (f :
 S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AlgebraicGeometry.AffineSpace.toSpecMvPoly.eq_1`：∀ (n : Type u) (S : Alg
ebraicGeometry.Scheme),   AlgebraicGeometry.AffineSpace.toSpecMvPoly n S =     C
ategoryTheory.Limits.pullback.snd (Ca…
· 使用引理 `AlgebraicGeometry.AffineSpace.map_toSpecMvPoly`：map_toSpecMvPoly {S T : 
Scheme.{u}} (f : S ⟶ T) : map n f ≫ toSpecMvPoly n T = toSpecMvPoly n S
-/
lemma isPullback_map {S T : Scheme.{u}} (f : S ⟶ T) :
    IsPullback (map n f) (𝔸(n; S) ↘ S) (𝔸(n; T) ↘ T) f := by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (map_over f)).mp ?_
  simp only [terminal.comp_from, ]
  convert! (IsPullback.of_hasPullback _ _).flip
  rw [← toSpecMvPoly, ← toSpecMvPoly, map_toSpecMvPoly]

/-- `𝔸(n; S)` is functorial w.r.t. `n`. -/
/-
**AlgebraicGeometry.AffineSpace.reindex** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.AffineSpace`。
形式化陈述：reindex {n m : Type u} (i : m -> n) (S : Scheme.{u}) : 𝔸(n; S) ⟶ 𝔸(m; S)
参数：i : m -> n；S : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`𝔸(n; S)` is functorial w.r.t. `n`.
-/
def reindex {n m : Type u} (i : m → n) (S : Scheme.{u}) : 𝔸(n; S) ⟶ 𝔸(m; S) :=
  homOfVector (𝔸(n; S) ↘ S) (coord S ∘ i)

@[simp, reassoc]
/-
**AlgebraicGeometry.AffineSpace.reindex_over** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.AffineSpace`。
形式化陈述：reindex_over {n m : Type u} (i : m -> n) (S : Scheme.{u}) : reindex i S ≫ 
𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S
参数：i : m -> n；S : Scheme.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma reindex_over {n m : Type u} (i : m → n) (S : Scheme.{u}) :
    reindex i S ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S :=
  pullback.lift_fst _ _ _

@[simp]
/-
**AlgebraicGeometry.AffineSpace.reindex_appTop_coord** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.AffineSpace`。
形式化陈述：reindex_appTop_coord {n m : Type u} (i : m -> n) (S : Scheme.{u}) (j : m) 
: (reindex i S).appTop (coord S j) = coord S (i j)
参数：i : m -> n；S : Scheme.{u}；j : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord`：homOfVector_appT
op_coord (i) : (homOfVector f v).appTop (coord S i) = v i
-/
lemma reindex_appTop_coord {n m : Type u} (i : m → n) (S : Scheme.{u}) (j : m) :
    (reindex i S).appTop (coord S j) = coord S (i j) :=
  homOfVector_appTop_coord _ _ _

@[simp]
/-
**AlgebraicGeometry.AffineSpace.reindex_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.AffineSpace`。
形式化陈述：reindex_id : reindex id S = 𝟙 𝔸(n; S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.AffineSpace.reindex_over`：reindex_over {n m : Type u} 
(i : m -> n) (S : Scheme.{u}) : reindex i S ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.instHomIsOverId`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.HomIsOver…
· 使用引理 `AlgebraicGeometry.AffineSpace.reindex_appTop_coord`：reindex_appTop_coord
 {n m : Type u} (i : m -> n) (S : Scheme.{u}) (j : m) : (reindex i S).appTop (co
ord S j) = coord S (i j)
-/
lemma reindex_id : reindex id S = 𝟙 𝔸(n; S) := by
  ext1 <;> simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/-
**AlgebraicGeometry.AffineSpace.reindex_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.AffineSpace`。
形式化陈述：reindex_comp {n₁ n₂ n₃ : Type u} (i : n₁ ⟶ n₂) (j : n₂ ⟶ n₃) (S : Scheme.{
u}) : reindex (i ≫ j) S = reindex j S ≫ reindex i S
参数：i : n₁ ⟶ n₂；j : n₂ ⟶ n₃；S : Scheme.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.AffineSpace.reindex_over`：reindex_over {n m : Type u} 
(i : m -> n) (S : Scheme.{u}) : reindex i S ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.AffineSpace.reindex_appTop_coord`：reindex_appTop_coord
 {n m : Type u} (i : m -> n) (S : Scheme.{u}) (j : m) : (reindex i S).appTop (co
ord S j) = coord S (i j)
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
lemma reindex_comp {n₁ n₂ n₃ : Type u} (i : n₁ ⟶ n₂) (j : n₂ ⟶ n₃) (S : Scheme.{u}) :
    reindex (i ≫ j) S = reindex j S ≫ reindex i S := by
  ext k <;> simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.AffineSpace.map_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.AffineSpace`。
形式化陈述：map_reindex {n₁ n₂ : Type u} (i : n₁ -> n₂) {S T : Scheme.{u}} (f : S ⟶ T)
 : map n₂ f ≫ reindex i T = reindex i S ≫ map n₁ f
参数：i : n₁ -> n₂；f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.AffineSpace.hom_ext`：hom_ext {f g : X ⟶ 𝔸(n; S)} (h₁ :
 f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S) (h₂ : forall i, f.appTop (coord S i) = g.app
Top (coord S i)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.AffineSpace.reindex_over`：reindex_over {n m : Type u} 
(i : m -> n) (S : Scheme.{u}) : reindex i S ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.AffineSpace.map_over`：map_over {S T : Scheme.{u}} (f :
 S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
· 使用定理 `CategoryTheory.comp_over_assoc`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X Y : C} (f : X ⟶ Y) (S : C)   [inst_1 : CategoryTheory.OverCl
ass X S] [inst_2 : C…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `AlgebraicGeometry.AffineSpace.reindex_appTop_coord`：reindex_appTop_coord
 {n m : Type u} (i : m -> n) (S : Scheme.{u}) (j : m) : (reindex i S).appTop (co
ord S j) = coord S (i j)
· 使用引理 `AlgebraicGeometry.AffineSpace.map_appTop_coord`：map_appTop_coord {S T : 
Scheme.{u}} (f : S ⟶ T) (i) : (map n f).appTop (coord T i) = coord S i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma map_reindex {n₁ n₂ : Type u} (i : n₁ → n₂) {S T : Scheme.{u}} (f : S ⟶ T) :
    map n₂ f ≫ reindex i T = reindex i S ≫ map n₁ f := by
  apply hom_ext <;> simp

/-- The affine space as a functor. -/
@[simps]
/-
**AlgebraicGeometry.AffineSpace.functor** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.AffineSpace`。
形式化陈述：functor : (Type u)ᵒᵖ ⥤ Scheme.{u} ⥤ Scheme.{u} where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine space as a functor.
-/
def functor : (Type u)ᵒᵖ ⥤ Scheme.{u} ⥤ Scheme.{u} where
  obj n := { obj := AffineSpace n.unop, map := map n.unop, map_id := map_id, map_comp := map_comp }
  map {n m} i := { app := reindex i.unop, naturality := fun _ _ ↦ map_reindex i.unop }
  map_id n := by ext : 2; exact reindex_id _
  map_comp f g := by ext : 2; dsimp; exact reindex_comp _ _ _

end functorial
section instances

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAffineHom (𝔸(n; S) ↘ S) := MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Surjective (𝔸(n; S) ↘ S) := MorphismProperty.pullback_fst _ _ <| by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)]
  exact ⟨MvPolynomial.comap_C_surjective⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite n] : LocallyOfFinitePresentation (𝔸(n; S) ↘ S) :=
  MorphismProperty.pullback_fst _ _ <| by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @LocallyOfFinitePresentation),
    HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), RingHom.FinitePresentation]
  convert! (inferInstance : Algebra.FinitePresentation (ULift ℤ) ℤ[n])
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl
/-
**AlgebraicGeometry.AffineSpace.isOpenMap_over** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.AffineSpace`。
形式化陈述：isOpenMap_over : IsOpenMap (𝔸(n; S) ↘ S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTopologicallyIsOpenMap`：(Algebrai
cGeometry.topologically fun {α β} [TopologicalSpace α] [TopologicalSpace β] => I
sOpenMap).RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `AlgebraicGeometry.AffineSpace.SpecIso_inv_over`：SpecIso_inv_over (R : Co
mmRingCat.{u}) : (SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R = Spec.map (CommRingC
at.ofHom C)
· 使用引理 `MvPolynomial.isOpenMap_comap_C`：isOpenMap_comap_C : IsOpenMap (comap (R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`：iff_of_openCo
ver (𝒰 : Y.OpenCover) : P f ↔ forall i, P (𝒰.pullbackHom f i)
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用引理 `AlgebraicGeometry.AffineSpace.isPullback_map`：isPullback_map {S T : Sche
me.{u}} (f : S ⟶ T) : IsPullback (map n f) (𝔸(n; S) ↘ S) (𝔸(n; T) ↘ T) f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
-/
lemma isOpenMap_over : IsOpenMap (𝔸(n; S) ↘ S) := by
  change topologically @IsOpenMap _
  wlog hS : ∃ R, S = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover
      (P := topologically @IsOpenMap) S.affineCover).mpr ?_
    intro i
    have := this (n := n) (S.affineCover.X i) ⟨_, rfl⟩
    rwa [← (isPullback_map (n := n) (S.affineCover.f i)).isoPullback_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)] at this
  obtain ⟨R, rfl⟩ := hS
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)
    (SpecIso n R).inv, SpecIso_inv_over]
  exact MvPolynomial.isOpenMap_comap_C
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GeometricallyIrreducible (𝔸(n; S) ↘ S) := by
  rw [geometricallyIrreducible_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IrreducibleSpace S] : IrreducibleSpace 𝔸(n; S) :=
  GeometricallyIrreducible.irreducibleSpace (𝔸(n; S) ↘ S) (isOpenMap_over S)
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GeometricallyReduced (𝔸(n; S) ↘ S) := by
  rw [geometricallyReduced_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : IsReduced S] : IsReduced 𝔸(n; S) := by
  wlog hS : ∃ R, S = Spec R
  · rw [IsReduced.iff_of_openCover _ (S.affineCover.pullback₁ (𝔸(n; S) ↘ S))]
    intro i
    have : IsReduced 𝔸(n; S.affineCover.X i) := this _ ⟨_, rfl⟩
    exact isReduced_of_isOpenImmersion ((isPullback_map _).isoPullback.inv)
  obtain ⟨R, rfl⟩ := hS
  rw [affine_isReduced_iff] at h
  exact isReduced_of_isOpenImmersion (SpecIso n R).hom
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GeometricallyIntegral (𝔸(n; S) ↘ S) :=
  .of_geometricallyReduced_of_geometricallyIrreducible _
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegral S] : IsIntegral 𝔸(n; S) := isIntegral_of_irreducibleSpace_of_isReduced _

set_option backward.isDefEq.respectTransparency.types false in
open MorphismProperty in
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty n] : IsIso (𝔸(n; S) ↘ S) := pullback_fst
    (P := isomorphisms _) _ _ <| by
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]
  apply IsStableUnderComposition.comp_mem
  · rw [HasAffineProperty.iff_of_isAffine (P := isomorphisms _), ← isomorphisms,
      ← arrow_mk_iso_iff (isomorphisms _) (arrowIsoΓSpecOfIsAffine _)]
    exact ⟨inferInstance, (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨C_injective n _, C_surjective _⟩⟩
  · exact isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.isIntegralHom_over_iff_isEmpty** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.AffineSpace`。
形式化陈述：isIntegralHom_over_iff_isEmpty : IsIntegralHom (𝔸(n; S) ↘ S) ↔ IsEmpty S ∨
 IsEmpty n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `not_isEmpty_of_nonempty`：not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsE
mpty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `RingHom.isIntegral_respectsIso`：isIntegral_respectsIso : RespectsIso fun
 f => f.IsIntegral
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.AffineSpace.SpecIso_inv_over`：SpecIso_inv_over (R : Co
mmRingCat.{u}) : (SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R = Spec.map (CommRingC
at.ofHom C)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.uniqueAlgEquiv_symm_apply`：∀ (R : Type u) [inst : CommSemir
ing R] (σ : Type u_2) [inst_1 : Unique σ] (p : Polynomial R),   (MvPolynomial.un
iqueAlgEquiv R σ).symm p = P…
· 使用定理 `Polynomial.algHom_eval₂_algebraMap`：algHom_eval₂_algebraMap {R A B : Typ
e*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] (p : 
R[X]) (f : A ->ₐ[R] B) (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 48 条，此处仅展示前 30 条）
-/
lemma isIntegralHom_over_iff_isEmpty : IsIntegralHom (𝔸(n; S) ↘ S) ↔ IsEmpty S ∨ IsEmpty n := by
  constructor
  · intro h
    cases isEmpty_or_nonempty S
    · exact .inl ‹_›
    refine .inr ?_
    wlog hS : ∃ R, S = Spec R
    · obtain ⟨x⟩ := ‹Nonempty S›
      obtain ⟨y, hy⟩ := S.affineCover.covers x
      exact this (S.affineCover.X _) (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_map (S.affineCover.f _)) h) ⟨y⟩ ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hS
    have : Nontrivial R := (subsingleton_or_nontrivial R).resolve_left fun H ↦
        not_isEmpty_of_nonempty (Spec R) (inferInstanceAs (IsEmpty (PrimeSpectrum R)))
    constructor
    intro i
    have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso.{u}
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom (SpecIso n R).inv,
      SpecIso_inv_over, HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)] at h
    obtain ⟨p : Polynomial R, hp, hp'⟩ :=
      (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
        (arrowIsoΓSpecOfIsAffine _)).mpr h.2 (X i)
    have : (rename fun _ ↦ i).comp (uniqueAlgEquiv.{_, u} _ PUnit).symm.toAlgHom p = 0 := by
      simp [← hp', ← algebraMap_eq]
    rw [AlgHom.comp_apply, map_eq_zero_iff _ (rename_injective _ (fun _ _ _ ↦ rfl))] at this
    simp only [AlgEquiv.coe_toAlgHom, EmbeddingLike.map_eq_zero_iff] at this
    simp [this] at hp
  · rintro (_ | _) <;> infer_instance
/-
**AlgebraicGeometry.AffineSpace.not_isIntegralHom** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.AffineSpace`。
形式化陈述：not_isIntegralHom [Nonempty S] [Nonempty n] : ¬ IsIntegralHom (𝔸(n; S) ↘ S
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_isIntegralHom [Nonempty S] [Nonempty n] : ¬ IsIntegralHom (𝔸(n; S) ↘ S) := by
  simp [isIntegralHom_over_iff_isEmpty]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.AffineSpace.spec_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.AffineSpace`。
形式化陈述：spec_le_iff (R : CommRingCat) (p q : Spec R) : p <= q ↔ q.asIdeal <= p.asI
deal
参数：R : CommRingCat；p q : Spec R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma spec_le_iff (R : CommRingCat) (p q : Spec R) : p ≤ q ↔ q.asIdeal ≤ p.asIdeal := by
  aesop (add simp PrimeSpectrum.le_iff_specializes)

/--
One should bear this equality in mind when breaking the `Spec R/ PrimeSpectrum R` abstraction
boundary, since these instances are not definitionally equal.
-/
/-
**AlgebraicGeometry.AffineSpace.** 是 Mathlib 中的一个示例，位于命名空间 `AlgebraicGeometry.Af
fineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One should bear this equality in mind when breaking the `Spec R/ PrimeSpectrum R
` abstraction
boundary, since these instances are not definitionally equal.
-/
example (R : CommRingCat) :
    inferInstance (α := Preorder (Spec R)) = inferInstance (α := Preorder (PrimeSpectrum R)ᵒᵈ) := by
  aesop (add simp spec_le_iff)

end instances

end AffineSpace

end AlgebraicGeometry

