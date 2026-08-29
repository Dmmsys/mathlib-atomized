/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The right Freyd category

Let `V` be a preadditive category. The right Freyd category of `V` is the quotient of
`Arrow V` by the right homotopy relation. (This is simply called "Freyd category"
in the reference.) This is a preadditive category with a fully
faithful additive functor `RightFreyd.functor : V ⥤ RightFreyd V`.

We also show that, if `V` has binary biproducts, then `RightFreyd V` has cokernels. In fact
we construct, given a morphism `f : u ⟶ v` in `Arrow V`, a morphism
`Candidate.π f : v ⟶ Candidate.cokernel f` in `Arrow V` such that
`f ≫ Candidate.π f` is right homotopic to `0` (see `Candidate.condition`).
This allows us to define a cokernel cofork for `(quotient V).map f` (see
`Candidate.cokernelCofork`), and we show in `Candidate.isColimitCokernelCofork` that this is
a cokernel cofork.

## References
* [Posur, S., *A constructive approach to Freyd categories*][posur2021Freyd]

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

/--
Definition of `RightFreyd` / `RightFreyd` 的定义

English:
definition RightFreyd
  body: CategoryTheory.Quotient (rightHomotopic V)

中文:
定义 RightFreyd
  定义体: CategoryTheory.Quotient (rightHomotopic V)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient, Quotient, rightHomotopic
-/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (RightFreyd V)
  body: inferInstanceAs Category (CategoryTheory.Quotient (rightHomotopic V))

中文:
实例 :
  签名: Category (RightFreyd V)
  定义体: inferInstanceAs Category (CategoryTheory.Quotient (rightHomotopic V))

Depends on / 依赖: Category, CategoryTheory, CategoryTheory.Quotient, Quotient, rightHomotopic
-/
instance : Category (RightFreyd V) :=
inferInstanceAs Category (CategoryTheory.Quotient (rightHomotopic V))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (RightFreyd V)
  body: Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

中文:
实例 :
  签名: Preadditive (RightFreyd V)
  定义体: Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

Depends on / 依赖: Quotient, Quotient.preadditive, RightHomotopy, RightHomotopy.add, preadditive
-/
instance : Preadditive (RightFreyd V) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

namespace RightFreyd

/--
Definition of `quotient` / `quotient` 的定义

English:
definition quotient
  signature: : Arrow V ⥤ RightFreyd V
  body: CategoryTheory.Quotient.functor _

中文:
定义 quotient
  签名: : Arrow V ⥤ RightFreyd V
  定义体: CategoryTheory.Quotient.functor _

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.functor, Quotient, functor
-/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient V).Full
  body: Quotient.full_functor _

中文:
实例 :
  签名: (quotient V).Full
  定义体: Quotient.full_functor _

Depends on / 依赖: Quotient, Quotient.full_functor, full_functor
-/
instance : (quotient V).Full := Quotient.full_functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient V).EssSurj
  body: Quotient.essSurj_functor _

中文:
实例 :
  签名: (quotient V).EssSurj
  定义体: Quotient.essSurj_functor _

Depends on / 依赖: Quotient, Quotient.essSurj_functor, essSurj_functor
-/
instance : (quotient V).EssSurj := Quotient.essSurj_functor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient V).Additive

中文:
实例 :
  签名: (quotient V).Additive
-/
instance : (quotient V).Additive where

variable {V}

/--
theorem `eq_of_rightHomotopy` / 定理 `eq_of_rightHomotopy`

English:
theorem eq_of_rightHomotopy
  given: {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g)
  proof: CategoryTheory.Quotient.sound _ ⟨h⟩

中文:
定理 eq_of_rightHomotopy
  条件: {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g)
  证明: CategoryTheory.Quotient.sound _ ⟨h⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.sound, Quotient
-/
theorem eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/--
Definition of `homotopyOfEq` / `homotopyOfEq` 的定义

English:
definition homotopyOfEq
  signature: {u v : Arrow V} (f g : u ⟶ v)
  body: ((Quotient.functor_map_eq_iff _ _ _).mp w).some

中文:
定义 homotopyOfEq
  签名: {u v : Arrow V} (f g : u ⟶ v)
  定义体: ((Quotient.functor_map_eq_iff _ _ _).mp w).some

Depends on / 依赖: Quotient, Quotient.functor_map_eq_iff, functor_map_eq_iff
-/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f g : u ⟶ v)

/--
lemma `quotient_map_eq_iff` / 引理 `quotient_map_eq_iff`

English:
lemma quotient_map_eq_iff
  proof: ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_rightHomotopy _ _ h⟩

中文:
引理 quotient_map_eq_iff
  证明: ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_rightHomotopy _ _ h⟩

Depends on / 依赖: eq_of_rightHomotopy, homotopyOfEq
-/
lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔ Nonempty (RightHomotopy f g) :=
  ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_rightHomotopy _ _ h⟩

/--
lemma `quotient_map_eq_zero_iff` / 引理 `quotient_map_eq_zero_iff`

English:
lemma quotient_map_eq_zero_iff
  statement: (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0)
  proof: ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_rightHomotopy _ _ h⟩

中文:
引理 quotient_map_eq_zero_iff
  结论: (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0)
  证明: ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_rightHomotopy _ _ h⟩

Depends on / 依赖: eq_of_rightHomotopy, homotopyOfEq
-/
lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h => ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ => by simpa using eq_of_rightHomotopy _ _ h⟩

/--
lemma `epi_of_isIso_right` / 引理 `epi_of_isIso_right`

English:
lemma epi_of_isIso_right
  given: [IsIso f.right]
  statement: Epi ((quotient V).map f) where
  proof: by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

中文:
引理 epi_of_isIso_right
  条件: [IsIso f.right]
  结论: Epi ((quotient V).map f) where
  证明: by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

Depends on / 依赖: RightHomotopy, eq_of_rightHomotopy, f.right, h.comm, h.hom, homotopyOfEq, map_surjective, quotient
-/
lemma epi_of_isIso_right [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

section Functor

variable [HasZeroObject V]

variable (V)

open ZeroObject in
set_option backward.defeqAttrib.useBackward true in
/-- If `V` has a zero object, this is the functor from `V` to `Arrow V`
that sends an object `X` to the arrow `0 ⟶ X`. -/
@[simps]
/--
Definition of `rightFunctor` / `rightFunctor` 的定义

English:
definition rightFunctor
  signature: : V ⥤ Arrow V where
  body: Arrow.mk (0 : 0 ⟶ X)
  map f := Arrow.homMk 0 f

中文:
定义 rightFunctor
  签名: : V ⥤ Arrow V where
  定义体: Arrow.mk (0 : 0 ⟶ X)
  map f := Arrow.homMk 0 f

Depends on / 依赖: Arrow.mk
-/
def rightFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk (0 : 0 ⟶ X)
  map f := Arrow.homMk 0 f

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (rightFunctor V).Additive
  body: by cat_disch

中文:
实例 :
  签名: (rightFunctor V).Additive
  定义体: by cat_disch

Depends on / 依赖: cat_disch
-/
instance : (rightFunctor V).Additive where
  map_add {_ _ _ _} := by cat_disch

/--
Definition of `functor` / `functor` 的定义

English:
abbreviation functor
  signature: : V ⥤ RightFreyd V
  body: rightFunctor V ⋙ quotient V

中文:
缩写 functor
  签名: : V ⥤ RightFreyd V
  定义体: rightFunctor V ⋙ quotient V

Depends on / 依赖: quotient, rightFunctor
-/
abbrev functor : V ⥤ RightFreyd V := rightFunctor V ⋙ quotient V

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor V).Additive
  body: by dsimp [functor]; infer_instance

中文:
实例 :
  签名: (functor V).Additive
  定义体: by dsimp [functor]; infer_instance

Depends on / 依赖: functor, infer_instance
-/
instance : (functor V).Additive := by dsimp [functor]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor V).Full
  body: by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    exact ⟨u.right, (quotient V).congr_map (by cat_disch)⟩

中文:
实例 :
  签名: (functor V).Full
  定义体: by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    exact ⟨u.right, (quotient V).congr_map (by cat_disch)⟩

Depends on / 依赖: cat_disch, congr_map, map_surjective, quotient, u.right
-/
instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    exact ⟨u.right, (quotient V).congr_map (by cat_disch)⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor V).Faithful
  body: by
    dsimp at eq
    rw [quotient_map_eq_iff] at eq
    simpa [← sub_eq_zero] using! eq.some.comm

中文:
实例 :
  签名: (functor V).Faithful
  定义体: by
    dsimp at eq
    rw [quotient_map_eq_iff] at eq
    simpa [← sub_eq_zero] using! eq.some.comm

Depends on / 依赖: eq.some.comm, quotient_map_eq_iff, sub_eq_zero
-/
instance : (functor V).Faithful where
  map_injective {_ _} f g eq := by
    dsimp at eq
    rw [quotient_map_eq_iff] at eq
    simpa [← sub_eq_zero] using! eq.some.comm

end Functor

variable [HasBinaryBiproducts V]

variable {u v : Arrow V} (f : u ⟶ v)

namespace Candidate

/--
Definition of `cokernel` / `cokernel` 的定义

English:
abbreviation cokernel
  body: Arrow.mk (biprod.desc v.hom f.right)

中文:
缩写 cokernel
  定义体: Arrow.mk (biprod.desc v.hom f.right)

Depends on / 依赖: Arrow.mk, biprod, biprod.desc, f.right, v.hom
-/
abbrev cokernel := Arrow.mk (biprod.desc v.hom f.right)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : v ⟶ cokernel f
  body: Arrow.homMk biprod.inl (𝟙 v.right)

中文:
定义 π
  签名: : v ⟶ cokernel f
  定义体: Arrow.homMk biprod.inl (𝟙 v.right)

Depends on / 依赖: Arrow.homMk, biprod, biprod.inl, v.right
-/
def π : v ⟶ cokernel f := Arrow.homMk biprod.inl (𝟙 v.right)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `condition` / `condition` 的定义

English:
definition condition
  signature: : RightHomotopy (f ≫ π f) 0 where
  body: biprod.inr
  comm := by simp [π]

中文:
定义 condition
  签名: : RightHomotopy (f ≫ π f) 0 where
  定义体: biprod.inr
  comm := by simp [π]

Depends on / 依赖: biprod, biprod.inr
-/
def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by simp [π]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi ((quotient V).map (π f))
  body: have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  epi_of_isIso_right _

中文:
实例 :
  签名: Epi ((quotient V).map (π f))
  定义体: have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  epi_of_isIso_right _

Depends on / 依赖: epi_of_isIso_right, homMk_right, infer_instance
-/
instance : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  epi_of_isIso_right _

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : cokernel f ⟶ w
  body: Arrow.homMk (biprod.desc g.left h.hom) g.right (biprod.hom_ext' _ _ (by simp)
    (by simp [← h.comm]))

中文:
定义 desc
  签名: : cokernel f ⟶ w
  定义体: Arrow.homMk (biprod.desc g.left h.hom) g.right (biprod.hom_ext' _ _ (by simp)
    (by simp [← h.comm]))

Depends on / 依赖: Arrow.homMk, biprod, biprod.desc, biprod.hom_ext, g.left, g.right, h.comm, h.hom, hom_ext
-/
def desc : cokernel f ⟶ w :=
  Arrow.homMk (biprod.desc g.left h.hom) g.right (biprod.hom_ext' _ _ (by simp)
    (by simp [← h.comm]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π_desc` / 引理 `π_desc`

English:
lemma π_desc
  statement: π f ≫ desc f g h = g
  proof: by ext <;> simp [π, desc]

中文:
引理 π_desc
  结论: π f ≫ desc f g h = g
  证明: by ext <;> simp [π, desc]
-/
lemma π_desc : π f ≫ desc f g h = g := by ext <;> simp [π, desc]

/--
Definition of `cokernelCofork` / `cokernelCofork` 的定义

English:
definition cokernelCofork
  signature: : CokernelCofork ((quotient V).map f)
  body: CokernelCofork.ofπ ((quotient V).map (Candidate.π f))
    (eq_of_rightHomotopy _ _ (Candidate.condition f))

中文:
定义 cokernelCofork
  签名: : CokernelCofork ((quotient V).map f)
  定义体: CokernelCofork.ofπ ((quotient V).map (Candidate.π f))
    (eq_of_rightHomotopy _ _ (Candidate.condition f))

Depends on / 依赖: Candidate, Candidate.condition, CokernelCofork, CokernelCofork.of, condition, eq_of_rightHomotopy, quotient
-/
def cokernelCofork : CokernelCofork ((quotient V).map f) :=
  CokernelCofork.ofπ ((quotient V).map (Candidate.π f))
    (eq_of_rightHomotopy _ _ (Candidate.condition f))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: : IsColimit (cokernelCofork f)
  body: CokernelCofork.IsColimit.ofπ' _
    (eq_of_rightHomotopy _ _ (Candidate.condition f))
    (fun g hg => Nonempty.some (by
      obtain ⟨g, rfl⟩ := (quotient V).map_surjective g
      exact ⟨(quotient V).map (desc f g (homotopyOfEq _ _ hg)),
        by simp [← Functor.map_comp]⟩))

中文:
定义 isColimitCokernelCofork
  签名: : IsColimit (cokernelCofork f)
  定义体: CokernelCofork.IsColimit.ofπ' _
    (eq_of_rightHomotopy _ _ (Candidate.condition f))
    (fun g hg => Nonempty.some (by
      obtain ⟨g, rfl⟩ := (quotient V).map_surjective g
      exact ⟨(quotient V).map (desc f g (homotopyOfEq _ _ hg)),
        by simp [← Functor.map_comp]⟩))

Depends on / 依赖: Candidate, Candidate.condition, CokernelCofork, CokernelCofork.IsColimit.of, Functor, Functor.map_comp, IsColimit, Nonempty, Nonempty.some, condition, eq_of_rightHomotopy, homotopyOfEq, map_comp, map_surjective, quotient
-/
def isColimitCokernelCofork : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ' _
    (eq_of_rightHomotopy _ _ (Candidate.condition f))
    (fun g hg => Nonempty.some (by
      obtain ⟨g, rfl⟩ := (quotient V).map_surjective g
      exact ⟨(quotient V).map (desc f g (homotopyOfEq _ _ hg)),
        by simp [← Functor.map_comp]⟩))

end Candidate

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCokernels (RightFreyd V)
  body: ⟨by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact ⟨_, Candidate.isColimitCokernelCofork f⟩⟩

中文:
实例 :
  签名: HasCokernels (RightFreyd V)
  定义体: ⟨by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact ⟨_, Candidate.isColimitCokernelCofork f⟩⟩

Depends on / 依赖: Candidate, Candidate.isColimitCokernelCofork, isColimitCokernelCofork, map_surjective, quotient
-/
instance : HasCokernels (RightFreyd V) where
  has_colimit f := ⟨by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact ⟨_, Candidate.isColimitCokernelCofork f⟩⟩

end RightFreyd

end CategoryTheory.Preadditive
