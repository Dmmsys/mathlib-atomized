/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.FinCases

/-!
# Simplicial sets

A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

-/

@[expose] public section

universe v u

open CategoryTheory Limits Functor ConcreteCategory

open Simplicial

/--
Definition of `SSet` / `SSet` 的定义

English:
abbreviation SSet
  signature: : Type (u + 1)
  body: SimplicialObject (Type u)

中文:
缩写 SSet
  签名: : Type (u + 1)
  定义体: SimplicialObject (Type u)

Depends on / 依赖: SimplicialObject
-/
abbrev SSet : Type (u + 1) :=
  SimplicialObject (Type u)

namespace SSet

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n = g.app n)
  statement: f = g
  proof: SimplicialObject.hom_ext _ _ w

@[simp]

中文:
引理 hom_ext
  条件: {X Y : SSet} {f g : X ⟶ Y} (w : 对任意 n, f.app n = g.app n)
  结论: f = g
  证明: SimplicialObject.hom_ext _ _ w

@[simp]

Depends on / 依赖: SimplicialObject, SimplicialObject.hom_ext, hom_ext
-/
lemma hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n = g.app n) : f = g :=
  SimplicialObject.hom_ext _ _ w

@[simp]
/--
lemma `id_app` / 引理 `id_app`

English:
lemma id_app
  given: (X : SSet) (n : SimplexCategoryᵒᵖ)
  proof: rfl

@[simp, reassoc]

中文:
引理 id_app
  条件: (X : SSet) (n : SimplexCategoryᵒᵖ)
  证明: rfl

@[simp, reassoc]
-/
lemma id_app (X : SSet) (n : SimplexCategoryᵒᵖ) :
    NatTrans.app (𝟙 X) n = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `comp_app` / 引理 `comp_app`

English:
lemma comp_app
  given: {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ)
  proof: rfl

中文:
引理 comp_app
  条件: {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ)
  证明: rfl
-/
lemma comp_app {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The constant map of simplicial sets `X ⟶ Y` induced by a simplex `y : Y _[0]`. -/
@[simps]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: {X Y : SSet.{u}} (y : Y _⦋0⦌)
  body: ↾fun _ => Y.map (n.unop.const _ 0).op y
  naturality _ _ _ := by
    ext
    dsimp
    rw [← CategoryTheory.comp_apply]; rw [← Functor.map_comp]
    rfl

@[simp]

中文:
定义 const
  签名: {X Y : SSet.{u}} (y : Y _⦋0⦌)
  定义体: ↾fun _ => Y.map (n.unop.const _ 0).op y
  naturality _ _ _ := by
    ext
    dsimp
    rw [← CategoryTheory.comp_apply]; rw [← Functor.map_comp]
    rfl

@[simp]

Depends on / 依赖: Y.map, n.unop.const
-/
def const {X Y : SSet.{u}} (y : Y _⦋0⦌) : X ⟶ Y where
  app n := ↾fun _ => Y.map (n.unop.const _ 0).op y
  naturality _ _ _ := by
    ext
    dsimp
    rw [← CategoryTheory.comp_apply]; rw [← Functor.map_comp]
    rfl

@[simp]
/--
lemma `comp_const` / 引理 `comp_const`

English:
lemma comp_const
  given: {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _⦋0⦌)
  proof: rfl

@[simp]

中文:
引理 comp_const
  条件: {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _⦋0⦌)
  证明: rfl

@[simp]
-/
lemma comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _⦋0⦌) :
    f ≫ const z = const z := rfl

@[simp]
/--
lemma `const_comp` / 引理 `const_comp`

English:
lemma const_comp
  given: {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z)
  proof: by
  cat_disch

中文:
引理 const_comp
  条件: {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch, g.app
-/
lemma const_comp {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  cat_disch

/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : SSet.{u} ⥤ SSet.{max u v}
  body: (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

中文:
定义 uliftFunctor
  签名: : SSet.{u} ⥤ SSet.{max u v}
  定义体: (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftFunctor, SimplicialObject, SimplicialObject.whiskering, uliftFunctor, whiskering
-/
def uliftFunctor : SSet.{u} ⥤ SSet.{max u v} :=
  (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

/--
Definition of `evaluation` / `evaluation` 的定义

English:
abbreviation evaluation
  signature: : SimplexCategoryᵒᵖ ⥤ SSet.{u} ⥤ Type u
  body: evaluation _ _

中文:
缩写 evaluation
  签名: : SimplexCategoryᵒᵖ ⥤ SSet.{u} ⥤ 类型u
  定义体: evaluation _ _
-/
protected abbrev evaluation : SimplexCategoryᵒᵖ ⥤ SSet.{u} ⥤ Type u :=
  evaluation _ _

/--
Definition of `Truncated` / `Truncated` 的定义

English:
abbreviation Truncated
  signature: (n : Nat)
  body: SimplicialObject.Truncated (Type u) n

中文:
缩写 Truncated
  签名: (n : 自然数)
  定义体: SimplicialObject.Truncated (Type u) n

Depends on / 依赖: SimplicialObject, SimplicialObject.Truncated, Truncated
-/
abbrev Truncated (n : Nat) := SimplicialObject.Truncated (Type u) n

namespace Truncated

/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: (k : Nat)
  body: (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]

中文:
定义 uliftFunctor
  签名: (k : 自然数)
  定义体: (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftFunctor, uliftFunctor, whiskeringRight
-/
def uliftFunctor (k : Nat) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {n : Nat} {X Y : Truncated n} {f g : X ⟶ Y} (w : forall n, f.app n = g.app n)
  proof: NatTrans.ext (funext w)

中文:
引理 hom_ext
  条件: {n : 自然数} {X Y : Truncated n} {f g : X ⟶ Y} (w : 对任意 n, f.app n = g.app n)
  证明: NatTrans.ext (funext w)

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma hom_ext {n : Nat} {X Y : Truncated n} {f g : X ⟶ Y} (w : forall n, f.app n = g.app n) :
    f = g :=
  NatTrans.ext (funext w)

/--
Definition of `trunc` / `trunc` 的定义

English:
abbreviation trunc
  signature: (n m : Nat) (h : m <= n := by lia)
  body: SimplicialObject.Truncated.trunc (Type u) n m

@[simp]

中文:
缩写 trunc
  签名: (n m : 自然数) (h : m <= n := by lia)
  定义体: SimplicialObject.Truncated.trunc (Type u) n m

@[simp]

Depends on / 依赖: SSet.Truncated, SimplicialObject, SimplicialObject.Truncated.trunc, Truncated
-/
abbrev trunc (n m : Nat) (h : m <= n := by lia) :
    SSet.Truncated n ⥤ SSet.Truncated m :=
  SimplicialObject.Truncated.trunc (Type u) n m

@[simp]
/--
lemma `id_app` / 引理 `id_app`

English:
lemma id_app
  given: {n : Nat} (X : Truncated n) (d : (SimplexCategory.Truncated n)ᵒᵖ)
  proof: rfl

@[simp, reassoc]

中文:
引理 id_app
  条件: {n : 自然数} (X : Truncated n) (d : (SimplexCategory.Truncated n)ᵒᵖ)
  证明: rfl

@[simp, reassoc]
-/
lemma id_app {n : Nat} (X : Truncated n) (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    NatTrans.app (𝟙 X) d = 𝟙 _ :=
  rfl

@[simp, reassoc]
/--
lemma `comp_app` / 引理 `comp_app`

English:
lemma comp_app
  statement: {n : Nat} {X Y Z : Truncated n} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 comp_app
  结论: {n : 自然数} {X Y Z : Truncated n} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma comp_app {n : Nat} {X Y Z : Truncated n} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    (f ≫ g).app d = f.app d ≫ g.app d :=
  rfl

end Truncated

/--
Definition of `truncation` / `truncation` 的定义

English:
abbreviation truncation
  signature: (n : Nat)
  body: SimplicialObject.truncation n

中文:
缩写 truncation
  签名: (n : 自然数)
  定义体: SimplicialObject.truncation n

Depends on / 依赖: SimplicialObject, SimplicialObject.truncation, truncation
-/
abbrev truncation (n : Nat) : SSet ⥤ SSet.Truncated n := SimplicialObject.truncation n

/--
Definition of `truncationCompTrunc` / `truncationCompTrunc` 的定义

English:
definition truncationCompTrunc
  signature: {n m : Nat} (h : m <= n)
  body: Iso.refl _

中文:
定义 truncationCompTrunc
  签名: {n m : 自然数} (h : m <= n)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def truncationCompTrunc {n m : Nat} (h : m <= n) :
    truncation n ⋙ Truncated.trunc n m ≅ truncation m :=
  Iso.refl _

open SimplexCategory

noncomputable section

/--
Definition of `Truncated.sk` / `Truncated.sk` 的定义

English:
abbreviation Truncated.sk
  signature: (n : Nat)
  body: SimplicialObject.Truncated.sk n

中文:
缩写 Truncated.sk
  签名: (n : 自然数)
  定义体: SimplicialObject.Truncated.sk n
-/
protected abbrev Truncated.sk (n : Nat) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.sk n

/--
Definition of `Truncated.cosk` / `Truncated.cosk` 的定义

English:
abbreviation Truncated.cosk
  signature: (n : Nat)
  body: SimplicialObject.Truncated.cosk n

中文:
缩写 Truncated.cosk
  签名: (n : 自然数)
  定义体: SimplicialObject.Truncated.cosk n
-/
protected abbrev Truncated.cosk (n : Nat) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.cosk n

/--
Definition of `sk` / `sk` 的定义

English:
abbreviation sk
  signature: (n : Nat)
  body: SimplicialObject.sk n

中文:
缩写 sk
  签名: (n : 自然数)
  定义体: SimplicialObject.sk n

Depends on / 依赖: SimplicialObject, SimplicialObject.sk
-/
abbrev sk (n : Nat) : SSet.{u} ⥤ SSet.{u} := SimplicialObject.sk n

/--
Definition of `cosk` / `cosk` 的定义

English:
abbreviation cosk
  signature: (n : Nat)
  body: SimplicialObject.cosk n

中文:
缩写 cosk
  签名: (n : 自然数)
  定义体: SimplicialObject.cosk n

Depends on / 依赖: SimplicialObject, SimplicialObject.cosk
-/
abbrev cosk (n : Nat) : SSet.{u} ⥤ SSet.{u} := SimplicialObject.cosk n

end

section adjunctions

/--
Definition of `skAdj` / `skAdj` 的定义

English:
definition skAdj
  signature: (n : Nat)
  body: SimplicialObject.skAdj n

中文:
定义 skAdj
  签名: (n : 自然数)
  定义体: SimplicialObject.skAdj n

Depends on / 依赖: SimplicialObject, SimplicialObject.skAdj
-/
noncomputable def skAdj (n : Nat) : Truncated.sk n ⊣ truncation.{u} n :=
  SimplicialObject.skAdj n

/--
Definition of `coskAdj` / `coskAdj` 的定义

English:
definition coskAdj
  signature: (n : Nat)
  body: SimplicialObject.coskAdj n

中文:
定义 coskAdj
  签名: (n : 自然数)
  定义体: SimplicialObject.coskAdj n

Depends on / 依赖: SimplicialObject, SimplicialObject.coskAdj, coskAdj
-/
noncomputable def coskAdj (n : Nat) : truncation.{u} n ⊣ Truncated.cosk n :=
  SimplicialObject.coskAdj n

namespace Truncated

/--
Instance `cosk_reflective` / 实例 `cosk_reflective`

English:
instance cosk_reflective
  signature: (n)
  body: SimplicialObject.Truncated.cosk_reflective n

中文:
实例 cosk_reflective
  签名: (n)
  定义体: SimplicialObject.Truncated.cosk_reflective n

Depends on / 依赖: SimplicialObject, SimplicialObject.Truncated.cosk_reflective, Truncated, cosk_reflective
-/
instance cosk_reflective (n) : IsIso (coskAdj n).counit :=
  SimplicialObject.Truncated.cosk_reflective n

/--
Instance `sk_coreflective` / 实例 `sk_coreflective`

English:
instance sk_coreflective
  signature: (n)
  body: SimplicialObject.Truncated.sk_coreflective n

中文:
实例 sk_coreflective
  签名: (n)
  定义体: SimplicialObject.Truncated.sk_coreflective n

Depends on / 依赖: SimplicialObject, SimplicialObject.Truncated.sk_coreflective, Truncated, sk_coreflective
-/
instance sk_coreflective (n) : IsIso (skAdj n).unit :=
  SimplicialObject.Truncated.sk_coreflective n

/--
Definition of `cosk.fullyFaithful` / `cosk.fullyFaithful` 的定义

English:
definition cosk.fullyFaithful
  signature: (n)
  body: SimplicialObject.Truncated.cosk.fullyFaithful n

中文:
定义 cosk.fullyFaithful
  签名: (n)
  定义体: SimplicialObject.Truncated.cosk.fullyFaithful n
-/
noncomputable def cosk.fullyFaithful (n) :
    (Truncated.cosk n).FullyFaithful :=
  SimplicialObject.Truncated.cosk.fullyFaithful n

/--
Instance `cosk.full` / 实例 `cosk.full`

English:
instance cosk.full
  signature: (n)
  body: SimplicialObject.Truncated.cosk.full n

中文:
实例 cosk.full
  签名: (n)
  定义体: SimplicialObject.Truncated.cosk.full n
-/
instance cosk.full (n) : (Truncated.cosk n).Full :=
  SimplicialObject.Truncated.cosk.full n

/--
Instance `cosk.faithful` / 实例 `cosk.faithful`

English:
instance cosk.faithful
  signature: (n)
  body: SimplicialObject.Truncated.cosk.faithful n

中文:
实例 cosk.faithful
  签名: (n)
  定义体: SimplicialObject.Truncated.cosk.faithful n

Depends on / 依赖: Module
-/
instance cosk.faithful (n) : (Truncated.cosk n).Faithful :=
  SimplicialObject.Truncated.cosk.faithful n

/--
Instance `coskAdj.reflective` / 实例 `coskAdj.reflective`

English:
instance coskAdj.reflective
  signature: (n)
  body: SimplicialObject.Truncated.coskAdj.reflective n

中文:
实例 coskAdj.reflective
  签名: (n)
  定义体: SimplicialObject.Truncated.coskAdj.reflective n
-/
noncomputable instance coskAdj.reflective (n) : Reflective (Truncated.cosk n) :=
  SimplicialObject.Truncated.coskAdj.reflective n

/--
Definition of `sk.fullyFaithful` / `sk.fullyFaithful` 的定义

English:
definition sk.fullyFaithful
  signature: (n)
  body: SimplicialObject.Truncated.sk.fullyFaithful n

中文:
定义 sk.fullyFaithful
  签名: (n)
  定义体: SimplicialObject.Truncated.sk.fullyFaithful n
-/
noncomputable def sk.fullyFaithful (n) :
    (Truncated.sk n).FullyFaithful := SimplicialObject.Truncated.sk.fullyFaithful n

/--
Instance `sk.full` / 实例 `sk.full`

English:
instance sk.full
  signature: (n)
  body: SimplicialObject.Truncated.sk.full n

中文:
实例 sk.full
  签名: (n)
  定义体: SimplicialObject.Truncated.sk.full n
-/
instance sk.full (n) : (Truncated.sk n).Full := SimplicialObject.Truncated.sk.full n

/--
Instance `sk.faithful` / 实例 `sk.faithful`

English:
instance sk.faithful
  signature: (n)
  body: SimplicialObject.Truncated.sk.faithful n

中文:
实例 sk.faithful
  签名: (n)
  定义体: SimplicialObject.Truncated.sk.faithful n
-/
instance sk.faithful (n) : (Truncated.sk n).Faithful :=
  SimplicialObject.Truncated.sk.faithful n

/--
Instance `skAdj.coreflective` / 实例 `skAdj.coreflective`

English:
instance skAdj.coreflective
  signature: (n)
  body: SimplicialObject.Truncated.skAdj.coreflective n

中文:
实例 skAdj.coreflective
  签名: (n)
  定义体: SimplicialObject.Truncated.skAdj.coreflective n
-/
noncomputable instance skAdj.coreflective (n) : Coreflective (Truncated.sk n) :=
  SimplicialObject.Truncated.skAdj.coreflective n

end Truncated

end adjunctions

/--
Definition of `Augmented` / `Augmented` 的定义

English:
abbreviation Augmented
  body: SimplicialObject.Augmented (Type u)

中文:
缩写 Augmented
  定义体: SimplicialObject.Augmented (Type u)

Depends on / 依赖: Augmented, SimplicialObject, SimplicialObject.Augmented
-/
abbrev Augmented :=
  SimplicialObject.Augmented (Type u)

section applications
variable {S : SSet}

/--
lemma `δ_comp_δ_apply` / 引理 `δ_comp_δ_apply`

English:
lemma δ_comp_δ_apply
  given: {n} {i j : Fin (n + 2)} (H : i <= j) (x : S _⦋n + 2⦌)
  proof: congr_hom (S.δ_comp_δ H) x

中文:
引理 δ_comp_δ_apply
  条件: {n} {i j : Fin (n + 2)} (H : i <= j) (x : S _⦋n + 2⦌)
  证明: congr_hom (S.δ_comp_δ H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_δ_apply {n} {i j : Fin (n + 2)} (H : i <= j) (x : S _⦋n + 2⦌) :
    S.δ i (S.δ j.succ x) = S.δ j (S.δ i.castSucc x) := congr_hom (S.δ_comp_δ H) x

/--
lemma `δ_comp_δ'_apply` / 引理 `δ_comp_δ'_apply`

English:
lemma δ_comp_δ'_apply
  statement: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
  proof: congr_hom (S.δ_comp_δ' H) x

中文:
引理 δ_comp_δ'_apply
  结论: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
  证明: congr_hom (S.δ_comp_δ' H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_δ'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
    (x : S _⦋n + 2⦌) : S.δ i (S.δ j x) =
      S.δ (j.pred H.ne_zero) (S.δ i.castSucc x) :=
  congr_hom (S.δ_comp_δ' H) x

/--
lemma `δ_comp_δ''_apply` / 引理 `δ_comp_δ''_apply`

English:
lemma δ_comp_δ''_apply
  statement: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
  proof: congr_hom (S.δ_comp_δ'' H) x

中文:
引理 δ_comp_δ''_apply
  结论: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
  证明: congr_hom (S.δ_comp_δ'' H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_δ''_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
    (x : S _⦋n + 2⦌) :
    S.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) (S.δ j.succ x) =
      S.δ j (S.δ i x) := congr_hom (S.δ_comp_δ'' H) x

/--
lemma `δ_comp_δ_self_apply` / 引理 `δ_comp_δ_self_apply`

English:
lemma δ_comp_δ_self_apply
  given: {n} {i : Fin (n + 2)} (x : S _⦋n + 2⦌)
  proof: congr_hom S.δ_comp_δ_self x

中文:
引理 δ_comp_δ_self_apply
  条件: {n} {i : Fin (n + 2)} (x : S _⦋n + 2⦌)
  证明: congr_hom S.δ_comp_δ_self x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_δ_self_apply {n} {i : Fin (n + 2)} (x : S _⦋n + 2⦌) :
    S.δ i (S.δ i.castSucc x) = S.δ i (S.δ i.succ x) := congr_hom S.δ_comp_δ_self x

/--
lemma `δ_comp_δ_self'_apply` / 引理 `δ_comp_δ_self'_apply`

English:
lemma δ_comp_δ_self'_apply
  statement: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
  proof: congr_hom (S.δ_comp_δ_self' H) x

中文:
引理 δ_comp_δ_self'_apply
  结论: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
  证明: congr_hom (S.δ_comp_δ_self' H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_δ_self'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
    (x : S _⦋n + 2⦌) : S.δ i (S.δ j x) = S.δ i (S.δ i.succ x) := congr_hom (S.δ_comp_δ_self' H) x

/--
lemma `δ_comp_σ_of_le_apply` / 引理 `δ_comp_σ_of_le_apply`

English:
lemma δ_comp_σ_of_le_apply
  statement: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j)
  proof: congr_hom (S.δ_comp_σ_of_le H) x

@[simp]

中文:
引理 δ_comp_σ_of_le_apply
  结论: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j)
  证明: congr_hom (S.δ_comp_σ_of_le H) x

@[simp]

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_of_le_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j)
    (x : S _⦋n + 1⦌) :
    S.δ (Fin.castSucc i) (S.σ j.succ x) = S.σ j (S.δ i x) := congr_hom (S.δ_comp_σ_of_le H) x

@[simp]
/--
lemma `δ_comp_σ_self_apply` / 引理 `δ_comp_σ_self_apply`

English:
lemma δ_comp_σ_self_apply
  given: {n} (i : Fin (n + 1)) (x : S _⦋n⦌)
  statement: S.δ i.castSucc (S.σ i x) = x
  proof: congr_hom S.δ_comp_σ_self x

中文:
引理 δ_comp_σ_self_apply
  条件: {n} (i : Fin (n + 1)) (x : S _⦋n⦌)
  结论: S.δ i.castSucc (S.σ i x) = x
  证明: congr_hom S.δ_comp_σ_self x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_self_apply {n} (i : Fin (n + 1)) (x : S _⦋n⦌) : S.δ i.castSucc (S.σ i x) = x :=
  congr_hom S.δ_comp_σ_self x

/--
lemma `δ_comp_σ_self'_apply` / 引理 `δ_comp_σ_self'_apply`

English:
lemma δ_comp_σ_self'_apply
  statement: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
  proof: congr_hom (S.δ_comp_σ_self' H) x

@[simp]

中文:
引理 δ_comp_σ_self'_apply
  结论: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
  证明: congr_hom (S.δ_comp_σ_self' H) x

@[simp]

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_self'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
    (x : S _⦋n⦌) : S.δ j (S.σ i x) = x := congr_hom (S.δ_comp_σ_self' H) x

@[simp]
/--
lemma `δ_comp_σ_succ_apply` / 引理 `δ_comp_σ_succ_apply`

English:
lemma δ_comp_σ_succ_apply
  given: {n} (i : Fin (n + 1)) (x : S _⦋n⦌)
  statement: S.δ i.succ (S.σ i x) = x
  proof: congr_hom S.δ_comp_σ_succ x

中文:
引理 δ_comp_σ_succ_apply
  条件: {n} (i : Fin (n + 1)) (x : S _⦋n⦌)
  结论: S.δ i.succ (S.σ i x) = x
  证明: congr_hom S.δ_comp_σ_succ x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_succ_apply {n} (i : Fin (n + 1)) (x : S _⦋n⦌) : S.δ i.succ (S.σ i x) = x :=
  congr_hom S.δ_comp_σ_succ x

/--
lemma `δ_comp_σ_succ'_apply` / 引理 `δ_comp_σ_succ'_apply`

English:
lemma δ_comp_σ_succ'_apply
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) (x : S _⦋n⦌)
  proof: congr_hom (S.δ_comp_σ_succ' H) x

中文:
引理 δ_comp_σ_succ'_apply
  条件: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) (x : S _⦋n⦌)
  证明: congr_hom (S.δ_comp_σ_succ' H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_succ'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) (x : S _⦋n⦌) :
    S.δ j (S.σ i x) = x := congr_hom (S.δ_comp_σ_succ' H) x

/--
lemma `δ_comp_σ_of_gt_apply` / 引理 `δ_comp_σ_of_gt_apply`

English:
lemma δ_comp_σ_of_gt_apply
  statement: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
  proof: congr_hom (S.δ_comp_σ_of_gt H) x

中文:
引理 δ_comp_σ_of_gt_apply
  结论: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
  证明: congr_hom (S.δ_comp_σ_of_gt H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_of_gt_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
    (x : S _⦋n + 1⦌) : S.δ i.succ (S.σ (Fin.castSucc j) x) = S.σ j (S.δ i x) :=
  congr_hom (S.δ_comp_σ_of_gt H) x

/--
lemma `δ_comp_σ_of_gt'_apply` / 引理 `δ_comp_σ_of_gt'_apply`

English:
lemma δ_comp_σ_of_gt'_apply
  statement: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
  proof: congr_hom (S.δ_comp_σ_of_gt' H) x

中文:
引理 δ_comp_σ_of_gt'_apply
  结论: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
  证明: congr_hom (S.δ_comp_σ_of_gt' H) x

Depends on / 依赖: congr_hom
-/
lemma δ_comp_σ_of_gt'_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
    (x : S _⦋n + 1⦌) : S.δ i (S.σ j x) =
      S.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le)))
        (S.δ (i.pred H.ne_zero) x) :=
  congr_hom (S.δ_comp_σ_of_gt' H) x

/--
lemma `σ_comp_σ_apply` / 引理 `σ_comp_σ_apply`

English:
lemma σ_comp_σ_apply
  given: {n} {i j : Fin (n + 1)} (H : i <= j) (x : S _⦋n⦌)
  proof: congr_hom (S.σ_comp_σ H) x

中文:
引理 σ_comp_σ_apply
  条件: {n} {i j : Fin (n + 1)} (H : i <= j) (x : S _⦋n⦌)
  证明: congr_hom (S.σ_comp_σ H) x

Depends on / 依赖: congr_hom
-/
lemma σ_comp_σ_apply {n} {i j : Fin (n + 1)} (H : i <= j) (x : S _⦋n⦌) :
    S.σ i.castSucc (S.σ j x) = S.σ j.succ (S.σ i x) := congr_hom (S.σ_comp_σ H) x

variable {T : SSet} (f : S ⟶ T)

open Opposite

/--
lemma `δ_naturality_apply` / 引理 `δ_naturality_apply`

English:
lemma δ_naturality_apply
  given: {n : Nat} (i : Fin (n + 2)) (x : S _⦋n + 1⦌)
  proof: by
  change (S.δ i ≫ f.app (op ⦋n⦌)) x = (f.app (op ⦋n + 1⦌) ≫ T.δ i) x
  exact congr_hom (SimplicialObject.δ_naturality f i) x

中文:
引理 δ_naturality_apply
  条件: {n : 自然数} (i : Fin (n + 2)) (x : S _⦋n + 1⦌)
  证明: by
  change (S.δ i ≫ f.app (op ⦋n⦌)) x = (f.app (op ⦋n + 1⦌) ≫ T.δ i) x
  exact congr_hom (SimplicialObject.δ_naturality f i) x

Depends on / 依赖: SimplicialObject, congr_hom, f.app
-/
lemma δ_naturality_apply {n : Nat} (i : Fin (n + 2)) (x : S _⦋n + 1⦌) :
    f.app (op ⦋n⦌) (S.δ i x) = T.δ i (f.app (op ⦋n + 1⦌) x) := by
  change (S.δ i ≫ f.app (op ⦋n⦌)) x = (f.app (op ⦋n + 1⦌) ≫ T.δ i) x
  exact congr_hom (SimplicialObject.δ_naturality f i) x

/--
lemma `σ_naturality_apply` / 引理 `σ_naturality_apply`

English:
lemma σ_naturality_apply
  given: {n : Nat} (i : Fin (n + 1)) (x : S _⦋n⦌)
  proof: by
  change (S.σ i ≫ f.app (op ⦋n + 1⦌)) x = (f.app (op ⦋n⦌) ≫ T.σ i) x
  exact congr_hom (SimplicialObject.σ_naturality f i) x

中文:
引理 σ_naturality_apply
  条件: {n : 自然数} (i : Fin (n + 1)) (x : S _⦋n⦌)
  证明: by
  change (S.σ i ≫ f.app (op ⦋n + 1⦌)) x = (f.app (op ⦋n⦌) ≫ T.σ i) x
  exact congr_hom (SimplicialObject.σ_naturality f i) x

Depends on / 依赖: SimplicialObject, congr_hom, f.app
-/
lemma σ_naturality_apply {n : Nat} (i : Fin (n + 1)) (x : S _⦋n⦌) :
    f.app (op ⦋n + 1⦌) (S.σ i x) = T.σ i (f.app (op ⦋n⦌) x) := by
  change (S.σ i ≫ f.app (op ⦋n + 1⦌)) x = (f.app (op ⦋n⦌) ≫ T.σ i) x
  exact congr_hom (SimplicialObject.σ_naturality f i) x

end applications

end SSet
