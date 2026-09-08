/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GluingOneHypercover
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Representability of schemes is a local property

In this file we prove that a sheaf of types `F` on `Sch` is representable if it is
locally representable.

## Main result
- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`:
  Suppose
  * F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
  * X : ι → Sch is a family of schemes
  * f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
  * f is jointly surjective

  Then `F` is representable.

## References
* https://stacks.math.columbia.edu/tag/01JJ

-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Category Limits Opposite

universe u

namespace Scheme

/-
Consider the following setup:
* F is `Type u`-valued a sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions

Later, we will also assume:
* The family f is locally surjective with respect to the Zariski topology
-/
variable (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → yoneda.obj (X i) ⟶ F.1) (hf : ∀ i, IsOpenImmersion.presheaf (f i))

namespace LocalRepresentability

variable {F f} (i j k : ι)

set_option backward.isDefEq.respectTransparency false in
open Functor.relativelyRepresentable in
/-- We get a family of gluing data by taking `U i = X i` and `V i j = (hf i).rep.pullback (f j)`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.glueData** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：glueData : GlueData where J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We get a family of gluing data by taking `U i = X i` and `V i j = (hf i).rep.pul
lback (f j)`.
-/
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := IsOpenImmersion.isIso_fst'_self IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [IsOpenImmersion.fst'_self_eq_snd IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

/-- The map from `X i` to the glued scheme `(glueData hf).glued` -/
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.toGlued** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：toGlued (i : ι) : X i ⟶ (glueData hf).glued
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `X i` to the glued scheme `(glueData hf).glued`
-/
noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.Scheme.LocalRepresentability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion (toGlued hf i) :=
  inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The map from the glued scheme `(glueData hf).glued`, treated as a sheaf, to `F`. -/
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.yonedaGluedToSheaf** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：yonedaGluedToSheaf : zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F wh
ere -- The map is obtained by finding an object of `F((glueData hf).glued)`. hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map from the glued scheme `(glueData hf).glued`, treated as a sheaf, to `F`.
-/
noncomputable def yonedaGluedToSheaf :
    zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F where
  -- The map is obtained by finding an object of `F((glueData hf).glued)`.
  hom := yonedaEquiv.symm
  -- This section is obtained from gluing the section corresponding to `f i : Hom(-, X i) ⟶ F`.
    ((glueData hf).sheafValGluedMk (fun i ↦ yonedaEquiv (f i)) (by
      intro i j
      apply yonedaEquiv.symm.injective
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f, glueData_t]
      rw [yonedaEquiv_naturality, Equiv.symm_apply_apply,
        Functor.map_comp_apply, yonedaEquiv_naturality, yonedaEquiv_naturality,
        Equiv.symm_apply_apply, ← Functor.map_comp_assoc,
        Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]))

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.yoneda_toGlued_yonedaGluedToShe
af** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：yoneda_toGlued_yonedaGluedToSheaf (i : ι) : yoneda.map (toGlued hf i) ≫ (y
onedaGluedToSheaf hf).hom = f i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.LocalRepresentability.yonedaGluedToSheaf.eq_1`：
∀ {F : CategoryTheory.Sheaf AlgebraicGeometry.Scheme.zariskiTopology (Type u)} {
ι : Type u}   {X : ι → AlgebraicGeometry.Scheme} {f : (i : ι…
· 使用定理 `CategoryTheory.yonedaEquiv_apply`：yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ T
ype v₁} (f : yoneda.obj X ⟶ F) : yonedaEquiv f = f.app (op X) (𝟙 X)
· 使用定理 `CategoryTheory.NatTrans.comp_app_apply`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F G H : CategoryT…
· 使用定理 `CategoryTheory.yoneda_map_app`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) (x : Cᵒᵖ),   (CategoryTheory.yoneda.map
 f).app x = TypeCat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `AlgebraicGeometry.Scheme.GlueData.sheafValGluedMk_val`：sheafValGluedMk_v
al (j : D.J) : F.obj.map (D.ι j).op (D.sheafValGluedMk s h) = s j
-/
lemma yoneda_toGlued_yonedaGluedToSheaf (i : ι) :
    yoneda.map (toGlued hf i) ≫ (yonedaGluedToSheaf hf).hom = f i := by
  apply yonedaEquiv.injective
  rw [yonedaGluedToSheaf, yonedaEquiv_apply, yonedaEquiv_apply,
    NatTrans.comp_app_apply, yoneda_map_app]
  simpa using! GlueData.sheafValGluedMk_val _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued*
* 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：yonedaGluedToSheaf_app_toGlued {i : ι} : dsimp% (yonedaGluedToSheaf hf).ho
m.app _ (toGlued hf i) = yonedaEquiv (f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.LocalRepresentability.yoneda_toGlued_yonedaGlue
dToSheaf`：yoneda_toGlued_yonedaGluedToSheaf (i : ι) : yoneda.map (toGlued hf i) 
≫ (yonedaGluedToSheaf hf).hom = f i
· 使用引理 `CategoryTheory.yonedaEquiv_comp`：yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ T
ype v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) : yonedaEquiv (α ≫ β) = β.app _ (yone
daEquiv α)
· 使用引理 `CategoryTheory.yonedaEquiv_yoneda_map`：yonedaEquiv_yoneda_map {X Y : C} 
(f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f
-/
lemma yonedaGluedToSheaf_app_toGlued {i : ι} :
    dsimp% (yonedaGluedToSheaf hf).hom.app _ (toGlued hf i) = yonedaEquiv (f i) := by
  rw [← yoneda_toGlued_yonedaGluedToSheaf hf i, yonedaEquiv_comp,
    yonedaEquiv_yoneda_map]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.yonedaGluedToSheaf_app_comp** 是
 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：yonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueD
ata hf).glued) : dsimp% (yonedaGluedToSheaf hf).hom.app (op V) (γ ≫ α) = F.obj.m
ap γ.op ((yonedaGluedToSheaf hf).hom.app (op U) α)
参数：γ : V ⟶ U；α : U ⟶ (glueData hf).glued。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma yonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued) :
    dsimp% (yonedaGluedToSheaf hf).hom.app (op V) (γ ≫ α) =
      F.obj.map γ.op ((yonedaGluedToSheaf hf).hom.app (op U) α) :=
  ConcreteCategory.congr_hom ((yonedaGluedToSheaf hf).hom.naturality γ.op) α

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.Scheme.LocalRepresentability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).hom = Sigma.desc f by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.comp_toGlued_eq** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：comp_toGlued_eq {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j) (h : yo
neda.map a ≫ f i = yoneda.map b ≫ f j) : a ≫ toGlued hf i = b ≫ toGlued hf j
参数：a : U ⟶ X i；b : U ⟶ X j；h : yoneda.map a ≫ f i = yoneda.map b ≫ f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.relative.rep`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.relativelyRepresentable.lift'_fst`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.relativelyRepresentable.lift'_snd`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.glue_condition`：glue_condition (i j : 
D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.relativelyRepresentable.symmetry_fst_assoc`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_toGlued_eq {U : Scheme} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  rw [← (hf i).rep.lift'_fst a b h, assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans (by simp [toGlued])

@[simp]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.glueData_openCover_map** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.Scheme.LocalRepresentability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ (α β : U ⟶ _) h
    replace h : (yonedaGluedToSheaf hf).hom.app _ α = (yonedaGluedToSheaf hf).hom.app _ β := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change γ ≫ α = γ ≫ β
    replace h : (yonedaGluedToSheaf hf).hom.app _ (γ ≫ α) =
        (yonedaGluedToSheaf hf).hom.app _ (γ ≫ β) := by dsimp at h; simp [h]
    rw [← fac₁, ← fac₂] at h ⊢
    apply comp_toGlued_eq
    simpa [Scheme.GlueData.openCover_X, yonedaEquiv_naturality] using h

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.Scheme.LocalRepresentability`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (yonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

/-- The isomorphism between `yoneda.obj (glueData hf).glued` and `F`.

This implies that `F` is representable. -/
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.yonedaIsoSheaf** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：yonedaIsoSheaf : zariskiTopology.yoneda.obj (glueData hf).glued ≅ F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.LocalRepresentability.instIsIsoSheafZariskiTopo
logyTypeYonedaGluedToSheaf`：∀ {F : CategoryTheory.Sheaf AlgebraicGeometry.Scheme
.zariskiTopology (Type u)} {ι : Type u}   {X : ι → AlgebraicGeometry.Scheme} {f 
: (i : ι…

--- 原说明 ---
The isomorphism between `yoneda.obj (glueData hf).glued` and `F`.

This implies that `F` is representable.
-/
noncomputable def yonedaIsoSheaf :
    zariskiTopology.yoneda.obj (glueData hf).glued ≅ F :=
  asIso (yonedaGluedToSheaf hf)

/--
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
* f is jointly surjective

Then `F` is representable, and the representing object is glued from the `X i`s
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.representableBy** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：representableBy : F.1.RepresentableBy (glueData hf).glued
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def representableBy : F.1.RepresentableBy (glueData hf).glued :=
  Functor.representableByEquiv.symm ((sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf))


include hf in
/--
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open immersions
* f is jointly surjective

Then `F` is representable.
-/
@[stacks 01JJ]
/-
**AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.Scheme.LocalRepresentability`。
形式化陈述：isRepresentable : F.1.IsRepresentable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
Suppose
* F is a `Type u`-valued sheaf on `Sch` with respect to the Zariski topology
* X : ι → Sch is a family of schemes
* f : Π i, yoneda.obj (X i) ⟶ F is a family of relatively representable open imm
ersions
* f is jointly surjective

Then `F` is representable.
-/
theorem isRepresentable : F.1.IsRepresentable :=
  ⟨_, ⟨representableBy hf⟩⟩

end LocalRepresentability

end Scheme

end AlgebraicGeometry

