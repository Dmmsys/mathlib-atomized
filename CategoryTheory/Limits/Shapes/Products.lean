/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`Discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `Fan` is a cone over a discrete category
* `Fan.mk` constructs a fan from an indexed collection of maps
* a `Pi` is a `limit (Discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

@[expose] public section

noncomputable section

universe w w' w₂ w₃ v v₂ u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w} {α : Type w₂} {γ : Type w₃}
variable {C : Type u} [Category.{v} C]

-- We don't need an analogue of `Pair` (for binary products), `ParallelPair` (for equalizers),
-- or `(Co)span`, since we already have `Discrete.functor`.

/--
Definition of `Fan` / `Fan` 的定义

English:
abbreviation Fan
  signature: (f : β -> C)
  body: Cone (Discrete.functor f)

中文:
缩写 Fan
  签名: (f : β -> C)
  定义体: Cone (Discrete.functor f)

Depends on / 依赖: Discrete, Discrete.functor, functor
-/
abbrev Fan (f : β -> C) :=
  Cone (Discrete.functor f)

/--
Definition of `Cofan` / `Cofan` 的定义

English:
abbreviation Cofan
  signature: (f : β -> C)
  body: Cocone (Discrete.functor f)

中文:
缩写 Cofan
  签名: (f : β -> C)
  定义体: Cocone (Discrete.functor f)

Depends on / 依赖: Cocone, Discrete, Discrete.functor, functor
-/
abbrev Cofan (f : β -> C) :=
  Cocone (Discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps! pt π_app, implicit_reducible]
/--
Definition of `Fan.mk` / `Fan.mk` 的定义

English:
definition Fan.mk
  signature: {f : β -> C} (P : C) (p : forall b, P ⟶ f b)
  body: P
  π := Discrete.natTrans (fun X => p X.as)

中文:
定义 Fan.mk
  签名: {f : β -> C} (P : C) (p : 对任意 b, P ⟶ f b)
  定义体: P
  π := Discrete.natTrans (fun X => p X.as)
-/
def Fan.mk {f : β -> C} (P : C) (p : forall b, P ⟶ f b) : Fan f where
  pt := P
  π := Discrete.natTrans (fun X => p X.as)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps! pt ι_app, implicit_reducible]
/--
Definition of `Cofan.mk` / `Cofan.mk` 的定义

English:
definition Cofan.mk
  signature: {f : β -> C} (P : C) (p : forall b, f b ⟶ P)
  body: P
  ι := Discrete.natTrans (fun X => p X.as)

中文:
定义 Cofan.mk
  签名: {f : β -> C} (P : C) (p : 对任意 b, f b ⟶ P)
  定义体: P
  ι := Discrete.natTrans (fun X => p X.as)
-/
def Cofan.mk {f : β -> C} (P : C) (p : forall b, f b ⟶ P) : Cofan f where
  pt := P
  ι := Discrete.natTrans (fun X => p X.as)

/--
Definition of `Fan.proj` / `Fan.proj` 的定义

English:
definition Fan.proj
  signature: {f : β -> C} (p : Fan f) (j : β)
  body: p.π.app (Discrete.mk j)

中文:
定义 Fan.proj
  签名: {f : β -> C} (p : Fan f) (j : β)
  定义体: p.π.app (Discrete.mk j)

Depends on / 依赖: Discrete, Discrete.mk
-/
def Fan.proj {f : β -> C} (p : Fan f) (j : β) : p.pt ⟶ f j :=
  p.π.app (Discrete.mk j)

/--
Definition of `Cofan.inj` / `Cofan.inj` 的定义

English:
definition Cofan.inj
  signature: {f : β -> C} (p : Cofan f) (j : β)
  body: p.ι.app (Discrete.mk j)

@[simp]

中文:
定义 Cofan.inj
  签名: {f : β -> C} (p : Cofan f) (j : β)
  定义体: p.ι.app (Discrete.mk j)

@[simp]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Discrete, Discrete.mk, Functor, Functor.LaxMonoidal.ofTensorHom, Iso.cancel_iso_inv_left, LaxMonoidal, associativity, associator_naturality, cancel_iso_inv_left, cat_disch, conv_lhs, conv_r, fun_, id_comp, ofTensorHom, tensorHom_comp_tensorHom, tensorHom_id
-/
def Cofan.inj {f : β -> C} (p : Cofan f) (j : β) : f j ⟶ p.pt :=
  p.ι.app (Discrete.mk j)

@[simp]
/--
theorem `fan_mk_proj` / 定理 `fan_mk_proj`

English:
theorem fan_mk_proj
  given: {f : β -> C} (P : C) (p : forall b, P ⟶ f b)
  statement: (Fan.mk P p).proj = p
  proof: rfl

@[simp]

中文:
定理 fan_mk_proj
  条件: {f : β -> C} (P : C) (p : 对任意 b, P ⟶ f b)
  结论: (Fan.mk P p).proj = p
  证明: rfl

@[simp]
-/
theorem fan_mk_proj {f : β -> C} (P : C) (p : forall b, P ⟶ f b) : (Fan.mk P p).proj = p :=
  rfl

@[simp]
/--
theorem `cofan_mk_inj` / 定理 `cofan_mk_inj`

English:
theorem cofan_mk_inj
  given: {f : β -> C} (P : C) (p : forall b, f b ⟶ P)
  statement: (Cofan.mk P p).inj = p
  proof: rfl

中文:
定理 cofan_mk_inj
  条件: {f : β -> C} (P : C) (p : 对任意 b, f b ⟶ P)
  结论: (Cofan.mk P p).inj = p
  证明: rfl
-/
theorem cofan_mk_inj {f : β -> C} (P : C) (p : forall b, f b ⟶ P) : (Cofan.mk P p).inj = p :=
  rfl

/--
Definition of `HasProduct` / `HasProduct` 的定义

English:
abbreviation HasProduct
  signature: (f : β -> C)
  body: HasLimit (Discrete.functor f)

中文:
缩写 HasProduct
  签名: (f : β -> C)
  定义体: HasLimit (Discrete.functor f)

Depends on / 依赖: Discrete, Discrete.functor, HasLimit, functor
-/
abbrev HasProduct (f : β -> C) :=
  HasLimit (Discrete.functor f)

/--
Definition of `HasCoproduct` / `HasCoproduct` 的定义

English:
abbreviation HasCoproduct
  signature: (f : β -> C)
  body: HasColimit (Discrete.functor f)

中文:
缩写 HasCoproduct
  签名: (f : β -> C)
  定义体: HasColimit (Discrete.functor f)

Depends on / 依赖: Discrete, Discrete.functor, HasColimit, functor
-/
abbrev HasCoproduct (f : β -> C) :=
  HasColimit (Discrete.functor f)

/--
lemma `hasCoproduct_of_equiv_of_iso` / 引理 `hasCoproduct_of_equiv_of_iso`

English:
lemma hasCoproduct_of_equiv_of_iso
  statement: (f : α -> C) (g : β -> C)
  proof: by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimit_of_iso α

中文:
引理 hasCoproduct_of_equiv_of_iso
  结论: (f : α -> C) (g : β -> C)
  证明: by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimit_of_iso α

Depends on / 依赖: Discrete, Discrete.equivalence, Discrete.functor, Discrete.natIso, equivalence, functor, hasColimit_of_iso, natIso
-/
lemma hasCoproduct_of_equiv_of_iso (f : α -> C) (g : β -> C)
    [HasCoproduct f] (e : β ≃ α) (iso : forall j, g j ≅ f (e j)) : HasCoproduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimit_of_iso α

/--
lemma `hasProduct_of_equiv_of_iso` / 引理 `hasProduct_of_equiv_of_iso`

English:
lemma hasProduct_of_equiv_of_iso
  statement: (f : α -> C) (g : β -> C)
  proof: by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasLimit_of_iso α.symm

中文:
引理 hasProduct_of_equiv_of_iso
  结论: (f : α -> C) (g : β -> C)
  证明: by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasLimit_of_iso α.symm

Depends on / 依赖: Discrete, Discrete.equivalence, Discrete.functor, Discrete.natIso, equivalence, functor, hasLimit_of_iso, natIso
-/
lemma hasProduct_of_equiv_of_iso (f : α -> C) (g : β -> C)
    [HasProduct f] (e : β ≃ α) (iso : forall j, g j ≅ f (e j)) : HasProduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasLimit_of_iso α.symm

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
/--
Definition of `Fan.IsLimit.mk` / `Fan.IsLimit.mk` 的定义

English:
definition Fan.IsLimit.mk
  signature: {f : β -> C} (t : Fan f) (lift : forall s : Fan f, s.pt ⟶ t.pt)
  body: { lift }

@[deprecated (since := "2026-05-19")]
alias mkFanLimit := Fan.IsLimit.mk

中文:
定义 Fan.是极限.mk
  签名: {f : β -> C} (t : Fan f) (lift : 对任意 s : Fan f, s.pt ⟶ t.pt)
  定义体: { lift }

@[deprecated (since := "2026-05-19")]
alias mkFanLimit := Fan.IsLimit.mk

Depends on / 依赖: IsLimit, cat_disch, s.proj, s.pt, t.proj, t.pt
-/
def Fan.IsLimit.mk {f : β -> C} (t : Fan f) (lift : forall s : Fan f, s.pt ⟶ t.pt)
    (fac : forall (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by cat_disch)
    (uniq : forall (s : Fan f) (m : s.pt ⟶ t.pt) (_ : forall j : β, m ≫ t.proj j = s.proj j),
      m = lift s := by cat_disch) :
    IsLimit t :=
  { lift }

@[deprecated (since := "2026-05-19")]
alias mkFanLimit := Fan.IsLimit.mk

/--
Definition of `Fan.IsLimit.lift` / `Fan.IsLimit.lift` 的定义

English:
definition Fan.IsLimit.lift
  signature: {F : β -> C} {c : Fan F} (hc : IsLimit c) {A : C}
  body: hc.lift (Fan.mk A f)

@[deprecated (since := "2026-01-12")] alias Fan.IsLimit.desc := Fan.IsLimit.lift

@[reassoc (attr := simp)]

中文:
定义 Fan.是极限.lift
  签名: {F : β -> C} {c : Fan F} (hc : 是极限 c) {A : C}
  定义体: hc.lift (Fan.mk A f)

@[deprecated (since := "2026-01-12")] alias Fan.IsLimit.desc := Fan.IsLimit.lift

@[reassoc (attr := simp)]

Depends on / 依赖: Fan.mk, hc.lift
-/
def Fan.IsLimit.lift {F : β -> C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : forall i, A ⟶ F i) : A ⟶ c.pt :=
  hc.lift (Fan.mk A f)

@[deprecated (since := "2026-01-12")] alias Fan.IsLimit.desc := Fan.IsLimit.lift

@[reassoc (attr := simp)]
/--
lemma `Fan.IsLimit.fac` / 引理 `Fan.IsLimit.fac`

English:
lemma Fan.IsLimit.fac
  statement: {F : β -> C} {c : Fan F} (hc : IsLimit c) {A : C}
  proof: hc.fac (Fan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]

中文:
引理 Fan.是极限.fac
  结论: {F : β -> C} {c : Fan F} (hc : 是极限 c) {A : C}
  证明: hc.fac (Fan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]

Depends on / 依赖: Fan.mk, hc.fac
-/
lemma Fan.IsLimit.fac {F : β -> C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : forall i, A ⟶ F i) (i : β) :
    Fan.IsLimit.lift hc f ≫ c.proj i = f i :=
  hc.fac (Fan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]
/--
lemma `Fan.IsLimit.lift_proj` / 引理 `Fan.IsLimit.lift_proj`

English:
lemma Fan.IsLimit.lift_proj
  statement: {X : β -> C} {c : Fan X} (d : Fan X) (hc : IsLimit c)
  proof: hc.fac _ _

中文:
引理 Fan.是极限.lift_proj
  结论: {X : β -> C} {c : Fan X} (d : Fan X) (hc : 是极限 c)
  证明: hc.fac _ _

Depends on / 依赖: hc.fac
-/
lemma Fan.IsLimit.lift_proj {X : β -> C} {c : Fan X} (d : Fan X) (hc : IsLimit c)
    (i : β) : hc.lift d ≫ c.proj i = d.proj i :=
  hc.fac _ _

/--
lemma `Fan.IsLimit.hom_ext` / 引理 `Fan.IsLimit.hom_ext`

English:
lemma Fan.IsLimit.hom_ext
  statement: {I : Type*} {F : I -> C} {c : Fan F} (hc : IsLimit c) {A : C}
  proof: hc.hom_ext (fun ⟨i⟩ => h i)

中文:
引理 Fan.是极限.hom_ext
  结论: {I : 类型} {F : I -> C} {c : Fan F} (hc : 是极限 c) {A : C}
  证明: hc.hom_ext (fun ⟨i⟩ => h i)

Depends on / 依赖: hc.hom_ext, hom_ext
-/
lemma Fan.IsLimit.hom_ext {I : Type*} {F : I -> C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f g : A ⟶ c.pt) (h : forall i, f ≫ c.proj i = g ≫ c.proj i) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

/-- Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
/--
Definition of `Cofan.IsColimit.mk` / `Cofan.IsColimit.mk` 的定义

English:
definition Cofan.IsColimit.mk
  signature: {f : β -> C} (s : Cofan f) (desc : forall t : Cofan f, s.pt ⟶ t.pt)
  body: { desc }

@[deprecated (since := "2026-05-19")]
alias mkCofanColimit := Cofan.IsColimit.mk

中文:
定义 Cofan.是余极限.mk
  签名: {f : β -> C} (s : Cofan f) (desc : 对任意 t : Cofan f, s.pt ⟶ t.pt)
  定义体: { desc }

@[deprecated (since := "2026-05-19")]
alias mkCofanColimit := Cofan.IsColimit.mk

Depends on / 依赖: IsColimit, cat_disch, s.inj, s.pt, t.inj, t.pt
-/
def Cofan.IsColimit.mk {f : β -> C} (s : Cofan f) (desc : forall t : Cofan f, s.pt ⟶ t.pt)
    (fac : forall (t : Cofan f) (j : β), s.inj j ≫ desc t = t.inj j := by cat_disch)
    (uniq : forall (t : Cofan f) (m : s.pt ⟶ t.pt) (_ : forall j : β, s.inj j ≫ m = t.inj j),
      m = desc t := by cat_disch) :
    IsColimit s :=
  { desc }

@[deprecated (since := "2026-05-19")]
alias mkCofanColimit := Cofan.IsColimit.mk

/--
Definition of `Cofan.IsColimit.desc` / `Cofan.IsColimit.desc` 的定义

English:
definition Cofan.IsColimit.desc
  signature: {F : β -> C} {c : Cofan F} (hc : IsColimit c) {A : C}
  body: hc.desc (Cofan.mk A f)

@[reassoc (attr := simp)]

中文:
定义 Cofan.是余极限.desc
  签名: {F : β -> C} {c : Cofan F} (hc : 是余极限 c) {A : C}
  定义体: hc.desc (Cofan.mk A f)

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.mk, hc.desc
-/
def Cofan.IsColimit.desc {F : β -> C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : forall i, F i ⟶ A) : c.pt ⟶ A :=
  hc.desc (Cofan.mk A f)

@[reassoc (attr := simp)]
/--
lemma `Cofan.IsColimit.fac` / 引理 `Cofan.IsColimit.fac`

English:
lemma Cofan.IsColimit.fac
  statement: {F : β -> C} {c : Cofan F} (hc : IsColimit c) {A : C}
  proof: hc.fac (Cofan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]

中文:
引理 Cofan.是余极限.fac
  结论: {F : β -> C} {c : Cofan F} (hc : 是余极限 c) {A : C}
  证明: hc.fac (Cofan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.mk, hc.fac
-/
lemma Cofan.IsColimit.fac {F : β -> C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : forall i, F i ⟶ A) (i : β) :
    c.inj i ≫ Cofan.IsColimit.desc hc f = f i :=
  hc.fac (Cofan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]
/--
lemma `Cofan.IsColimit.inj_desc` / 引理 `Cofan.IsColimit.inj_desc`

English:
lemma Cofan.IsColimit.inj_desc
  statement: {X : β -> C} {c : Cofan X} (d : Cofan X) (hc : IsColimit c)
  proof: hc.fac _ _

中文:
引理 Cofan.是余极限.inj_desc
  结论: {X : β -> C} {c : Cofan X} (d : Cofan X) (hc : 是余极限 c)
  证明: hc.fac _ _

Depends on / 依赖: hc.fac
-/
lemma Cofan.IsColimit.inj_desc {X : β -> C} {c : Cofan X} (d : Cofan X) (hc : IsColimit c)
    (i : β) : c.inj i ≫ hc.desc d = d.inj i :=
  hc.fac _ _

/--
lemma `Cofan.IsColimit.hom_ext` / 引理 `Cofan.IsColimit.hom_ext`

English:
lemma Cofan.IsColimit.hom_ext
  statement: {I : Type*} {F : I -> C} {c : Cofan F} (hc : IsColimit c) {A : C}
  proof: hc.hom_ext (fun ⟨i⟩ => h i)

中文:
引理 Cofan.是余极限.hom_ext
  结论: {I : 类型} {F : I -> C} {c : Cofan F} (hc : 是余极限 c) {A : C}
  证明: hc.hom_ext (fun ⟨i⟩ => h i)

Depends on / 依赖: hc.hom_ext, hom_ext
-/
lemma Cofan.IsColimit.hom_ext {I : Type*} {F : I -> C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f g : c.pt ⟶ A) (h : forall i, c.inj i ≫ f = c.inj i ≫ g) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

section

variable (C)

/--
Definition of `HasProductsOfShape` / `HasProductsOfShape` 的定义

English:
abbreviation HasProductsOfShape
  signature: (β : Type v)
  body: HasLimitsOfShape.{v} (Discrete β)

中文:
缩写 HasProductsOfShape
  签名: (β : 类型v)
  定义体: HasLimitsOfShape.{v} (Discrete β)

Depends on / 依赖: Discrete, HasLimitsOfShape
-/
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)

/--
Definition of `HasCoproductsOfShape` / `HasCoproductsOfShape` 的定义

English:
abbreviation HasCoproductsOfShape
  signature: (β : Type v)
  body: HasColimitsOfShape.{v} (Discrete β)

中文:
缩写 HasCoproductsOfShape
  签名: (β : 类型v)
  定义体: HasColimitsOfShape.{v} (Discrete β)

Depends on / 依赖: Discrete, HasColimitsOfShape
-/
abbrev HasCoproductsOfShape (β : Type v) :=
  HasColimitsOfShape.{v} (Discrete β)

end

/--
Definition of `piObj` / `piObj` 的定义

English:
abbreviation piObj
  signature: (f : β -> C) [HasProduct f]
  body: limit (Discrete.functor f)

中文:
缩写 piObj
  签名: (f : β -> C) [HasProduct f]
  定义体: limit (Discrete.functor f)

Depends on / 依赖: Discrete, Discrete.functor, functor
-/
abbrev piObj (f : β -> C) [HasProduct f] :=
  limit (Discrete.functor f)

/--
Definition of `sigmaObj` / `sigmaObj` 的定义

English:
abbreviation sigmaObj
  signature: (f : β -> C) [HasCoproduct f]
  body: colimit (Discrete.functor f)

中文:
缩写 sigmaObj
  签名: (f : β -> C) [HasCoproduct f]
  定义体: colimit (Discrete.functor f)

Depends on / 依赖: Discrete, Discrete.functor, colimit, functor
-/
abbrev sigmaObj (f : β -> C) [HasCoproduct f] :=
  colimit (Discrete.functor f)

/-- notation for categorical products. We need `ᶜ` to avoid conflict with `Finset.prod`. -/
notation "∏ᶜ " f:60 => piObj f

/-- notation for categorical coproducts -/
notation "∐ " f:60 => sigmaObj f

/--
Definition of `Pi.π` / `Pi.π` 的定义

English:
abbreviation Pi.π
  signature: (f : β -> C) [HasProduct f] (b : β)
  body: limit.π (Discrete.functor f) (Discrete.mk b)

中文:
缩写 依赖函数类型.π
  签名: (f : β -> C) [HasProduct f] (b : β)
  定义体: limit.π (Discrete.functor f) (Discrete.mk b)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, functor
-/
abbrev Pi.π (f : β -> C) [HasProduct f] (b : β) : ∏ᶜ f ⟶ f b :=
  limit.π (Discrete.functor f) (Discrete.mk b)

/--
Definition of `Sigma.ι` / `Sigma.ι` 的定义

English:
abbreviation Sigma.ι
  signature: (f : β -> C) [HasCoproduct f] (b : β)
  body: colimit.ι (Discrete.functor f) (Discrete.mk b)

中文:
缩写 依赖和类型.ι
  签名: (f : β -> C) [HasCoproduct f] (b : β)
  定义体: colimit.ι (Discrete.functor f) (Discrete.mk b)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, colimit, functor
-/
abbrev Sigma.ι (f : β -> C) [HasCoproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (Discrete.functor f) (Discrete.mk b)

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[ext 1050]
/--
lemma `Pi.hom_ext` / 引理 `Pi.hom_ext`

English:
lemma Pi.hom_ext
  statement: {f : β -> C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
  proof: limit.hom_ext (fun ⟨j⟩ => h j)

中文:
引理 依赖函数类型.hom_ext
  结论: {f : β -> C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
  证明: limit.hom_ext (fun ⟨j⟩ => h j)

Depends on / 依赖: hom_ext, limit.hom_ext
-/
lemma Pi.hom_ext {f : β -> C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
    (h : forall (b : β), g₁ ≫ Pi.π f b = g₂ ≫ Pi.π f b) : g₁ = g₂ :=
  limit.hom_ext (fun ⟨j⟩ => h j)

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[ext 1050]
/--
lemma `Sigma.hom_ext` / 引理 `Sigma.hom_ext`

English:
lemma Sigma.hom_ext
  statement: {f : β -> C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
  proof: colimit.hom_ext (fun ⟨j⟩ => h j)

中文:
引理 依赖和类型.hom_ext
  结论: {f : β -> C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
  证明: colimit.hom_ext (fun ⟨j⟩ => h j)

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext
-/
lemma Sigma.hom_ext {f : β -> C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
    (h : forall (b : β), Sigma.ι f b ≫ g₁ = Sigma.ι f b ≫ g₂) : g₁ = g₂ :=
  colimit.hom_ext (fun ⟨j⟩ => h j)

/--
Definition of `productIsProduct` / `productIsProduct` 的定义

English:
definition productIsProduct
  signature: (f : β -> C) [HasProduct f]
  body: IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cone.ext (Iso.refl _))

中文:
定义 productIsProduct
  签名: (f : β -> C) [HasProduct f]
  定义体: IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cone.ext (Iso.refl _))

Depends on / 依赖: Cone.ext, Discrete, Discrete.functor, IsLimit, IsLimit.ofIsoLimit, Iso.refl, functor, isLimit, limit.isLimit, ofIsoLimit
-/
def productIsProduct (f : β -> C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cone.ext (Iso.refl _))

/--
Definition of `coproductIsCoproduct` / `coproductIsCoproduct` 的定义

English:
definition coproductIsCoproduct
  signature: (f : β -> C) [HasCoproduct f]
  body: IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocone.ext (Iso.refl _))

中文:
定义 coproductIsCoproduct
  签名: (f : β -> C) [HasCoproduct f]
  定义体: IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocone.ext (Iso.refl _))

Depends on / 依赖: Cocone, Cocone.ext, Discrete, Discrete.functor, IsColimit, IsColimit.ofIsoColimit, Iso.refl, colimit, colimit.isColimit, functor, isColimit, ofIsoColimit
-/
def coproductIsCoproduct (f : β -> C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocone.ext (Iso.refl _))

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[reassoc]
/--
theorem `Pi.π_comp_eqToHom` / 定理 `Pi.π_comp_eqToHom`

English:
theorem Pi.π_comp_eqToHom
  given: {J : Type*} (f : J -> C) [HasProduct f] {j j' : J} (w : j = j')
  proof: by
  simp [*]

@[reassoc (attr := simp)]

中文:
定理 依赖函数类型.π_comp_eqToHom
  条件: {J : 类型} (f : J -> C) [HasProduct f] {j j' : J} (w : j = j')
  证明: by
  simp [*]

@[reassoc (attr := simp)]
-/
theorem Pi.π_comp_eqToHom {J : Type*} (f : J -> C) [HasProduct f] {j j' : J} (w : j = j') :
    Pi.π f j ≫ eqToHom (by simp [w]) = Pi.π f j' := by
  simp [*]

@[reassoc (attr := simp)]
/--
theorem `Sigma.eqToHom_comp_ι` / 定理 `Sigma.eqToHom_comp_ι`

English:
theorem Sigma.eqToHom_comp_ι
  given: {J : Type*} (f : J -> C) [HasCoproduct f] {j j' : J} (w : j = j')
  proof: by
  cases w
  simp

中文:
定理 依赖和类型.eqToHom_comp_ι
  条件: {J : 类型} (f : J -> C) [HasCoproduct f] {j j' : J} (w : j = j')
  证明: by
  cases w
  simp
-/
theorem Sigma.eqToHom_comp_ι {J : Type*} (f : J -> C) [HasCoproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ Sigma.ι f j' = Sigma.ι f j := by
  cases w
  simp

/--
Definition of `Pi.lift` / `Pi.lift` 的定义

English:
abbreviation Pi.lift
  signature: {f : β -> C} [HasProduct f] {P : C} (p : forall b, P ⟶ f b)
  body: limit.lift _ (Fan.mk P p)

@[reassoc, elementwise]

中文:
缩写 依赖函数类型.lift
  签名: {f : β -> C} [HasProduct f] {P : C} (p : 对任意 b, P ⟶ f b)
  定义体: limit.lift _ (Fan.mk P p)

@[reassoc, elementwise]

Depends on / 依赖: Fan.mk, limit.lift
-/
abbrev Pi.lift {f : β -> C} [HasProduct f] {P : C} (p : forall b, P ⟶ f b) : P ⟶ ∏ᶜ f :=
  limit.lift _ (Fan.mk P p)

@[reassoc, elementwise]
/--
theorem `Pi.lift_π` / 定理 `Pi.lift_π`

English:
theorem Pi.lift_π
  given: {β : Type w} {f : β -> C} [HasProduct f] {P : C} (p : forall b, P ⟶ f b) (b : β)
  proof: by
  simp only [limit.lift_π, Fan.mk_π_app]

中文:
定理 依赖函数类型.lift_π
  条件: {β : 类型 w} {f : β -> C} [HasProduct f] {P : C} (p : 对任意 b, P ⟶ f b) (b : β)
  证明: by
  simp only [limit.lift_π, Fan.mk_π_app]

Depends on / 依赖: Fan.mk_, limit.lift_
-/
theorem Pi.lift_π {β : Type w} {f : β -> C} [HasProduct f] {P : C} (p : forall b, P ⟶ f b) (b : β) :
    Pi.lift p ≫ Pi.π f b = p b := by
  simp only [limit.lift_π, Fan.mk_π_app]

/-- A version of `Cone.ext` for `Fan`s. -/
@[simps!]
/--
Definition of `Fan.ext` / `Fan.ext` 的定义

English:
definition Fan.ext
  signature: {f : β -> C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
  body: Cone.ext e (fun ⟨j⟩ => w j)

中文:
定义 Fan.ext
  签名: {f : β -> C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
  定义体: Cone.ext e (fun ⟨j⟩ => w j)

Depends on / 依赖: Cone.ext, cat_disch
-/
def Fan.ext {f : β -> C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
    (w : forall (b : β), c₁.proj b = e.hom ≫ c₂.proj b := by cat_disch) : c₁ ≅ c₂ :=
  Cone.ext e (fun ⟨j⟩ => w j)

/--
Definition of `Fan.isLimitOfIsIsoPiLift` / `Fan.isLimitOfIsIsoPiLift` 的定义

English:
definition Fan.isLimitOfIsIsoPiLift
  signature: {f : β -> C} [HasProduct f] (c : Fan f)
  body: IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Fan.ext (@asIso _ _ _ _ _ hc) (fun _ => (limit.lift_π _ _).symm)).symm

中文:
定义 Fan.isLimitOfIsIsoPiLift
  签名: {f : β -> C} [HasProduct f] (c : Fan f)
  定义体: IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Fan.ext (@asIso _ _ _ _ _ hc) (fun _ => (limit.lift_π _ _).symm)).symm

Depends on / 依赖: Discrete, Discrete.functor, Fan.ext, IsLimit, IsLimit.ofIsoLimit, functor, isLimit, limit.isLimit, limit.lift_, ofIsoLimit
-/
def Fan.isLimitOfIsIsoPiLift {f : β -> C} [HasProduct f] (c : Fan f)
    [hc : IsIso (Pi.lift c.proj)] : IsLimit c :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Fan.ext (@asIso _ _ _ _ _ hc) (fun _ => (limit.lift_π _ _).symm)).symm

/--
lemma `Fan.nonempty_isLimit_iff_isIso_piLift` / 引理 `Fan.nonempty_isLimit_iff_isIso_piLift`

English:
lemma Fan.nonempty_isLimit_iff_isIso_piLift
  given: {f : β -> C} [HasProduct f] (c : Fan f)
  proof: (limit.isLimit (Discrete.functor f)).nonempty_isLimit_iff_isIso_lift

中文:
引理 Fan.nonempty_isLimit_iff_isIso_piLift
  条件: {f : β -> C} [HasProduct f] (c : Fan f)
  证明: (limit.isLimit (Discrete.functor f)).nonempty_isLimit_iff_isIso_lift

Depends on / 依赖: Discrete, Discrete.functor, functor, isLimit, limit.isLimit, nonempty_isLimit_iff_isIso_lift
-/
lemma Fan.nonempty_isLimit_iff_isIso_piLift {f : β -> C} [HasProduct f] (c : Fan f) :
    Nonempty (IsLimit c) ↔ IsIso (Pi.lift c.proj) :=
  (limit.isLimit (Discrete.functor f)).nonempty_isLimit_iff_isIso_lift

/--
Definition of `Sigma.desc` / `Sigma.desc` 的定义

English:
abbreviation Sigma.desc
  signature: {f : β -> C} [HasCoproduct f] {P : C} (p : forall b, f b ⟶ P)
  body: colimit.desc _ (Cofan.mk P p)

@[reassoc]

中文:
缩写 依赖和类型.desc
  签名: {f : β -> C} [HasCoproduct f] {P : C} (p : 对任意 b, f b ⟶ P)
  定义体: colimit.desc _ (Cofan.mk P p)

@[reassoc]

Depends on / 依赖: Cofan.mk, colimit, colimit.desc
-/
abbrev Sigma.desc {f : β -> C} [HasCoproduct f] {P : C} (p : forall b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)

@[reassoc]
/--
theorem `Sigma.ι_desc` / 定理 `Sigma.ι_desc`

English:
theorem Sigma.ι_desc
  given: {β : Type w} {f : β -> C} [HasCoproduct f] {P : C} (p : forall b, f b ⟶ P) (b : β)
  proof: by
  simp only [colimit.ι_desc, Cofan.mk_ι_app]

中文:
定理 依赖和类型.ι_desc
  条件: {β : 类型 w} {f : β -> C} [HasCoproduct f] {P : C} (p : 对任意 b, f b ⟶ P) (b : β)
  证明: by
  simp only [colimit.ι_desc, Cofan.mk_ι_app]

Depends on / 依赖: Cofan.mk_, colimit
-/
theorem Sigma.ι_desc {β : Type w} {f : β -> C} [HasCoproduct f] {P : C} (p : forall b, f b ⟶ P) (b : β) :
    Sigma.ι f b ≫ Sigma.desc p = p b := by
  simp only [colimit.ι_desc, Cofan.mk_ι_app]

instance {f : β -> C} [HasCoproduct f] : IsIso (Sigma.desc (fun a => Sigma.ι f a)) := by
  convert! IsIso.id _
  ext
  simp

/-- A version of `Cocone.ext` for `Cofan`s. -/
@[simps!]
/--
Definition of `Cofan.ext` / `Cofan.ext` 的定义

English:
definition Cofan.ext
  signature: {f : β -> C} {c₁ c₂ : Cofan f} (e : c₁.pt ≅ c₂.pt)
  body: Cocone.ext e (fun ⟨j⟩ => w j)

中文:
定义 Cofan.ext
  签名: {f : β -> C} {c₁ c₂ : Cofan f} (e : c₁.pt ≅ c₂.pt)
  定义体: Cocone.ext e (fun ⟨j⟩ => w j)

Depends on / 依赖: Cocone, Cocone.ext, cat_disch
-/
def Cofan.ext {f : β -> C} {c₁ c₂ : Cofan f} (e : c₁.pt ≅ c₂.pt)
    (w : forall (b : β), c₁.inj b ≫ e.hom = c₂.inj b := by cat_disch) : c₁ ≅ c₂ :=
  Cocone.ext e (fun ⟨j⟩ => w j)

/--
Definition of `Cofan.isColimitOfIsIsoSigmaDesc` / `Cofan.isColimitOfIsIsoSigmaDesc` 的定义

English:
definition Cofan.isColimitOfIsIsoSigmaDesc
  signature: {f : β -> C} [HasCoproduct f] (c : Cofan f)
  body: IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cofan.ext (@asIso _ _ _ _ _ hc) (fun _ => colimit.ι_desc _ _))

中文:
定义 Cofan.isColimitOfIsIsoSigmaDesc
  签名: {f : β -> C} [HasCoproduct f] (c : Cofan f)
  定义体: IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cofan.ext (@asIso _ _ _ _ _ hc) (fun _ => colimit.ι_desc _ _))

Depends on / 依赖: Cofan.ext, Discrete, Discrete.functor, IsColimit, IsColimit.ofIsoColimit, colimit, colimit.isColimit, functor, isColimit, ofIsoColimit
-/
def Cofan.isColimitOfIsIsoSigmaDesc {f : β -> C} [HasCoproduct f] (c : Cofan f)
    [hc : IsIso (Sigma.desc c.inj)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cofan.ext (@asIso _ _ _ _ _ hc) (fun _ => colimit.ι_desc _ _))

/--
lemma `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc` / 引理 `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc`

English:
lemma Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
  given: {f : β -> C} [HasCoproduct f] (c : Cofan f)
  proof: (colimit.isColimit (Discrete.functor f)).nonempty_isColimit_iff_isIso_desc

@[deprecated (since := "2026-01-21")]
alias Cofan.isColimit_iff_isIso_sigmaDesc := Cofan.nonempty_isColimit_iff_isIso_sigmaDesc

中文:
引理 Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
  条件: {f : β -> C} [HasCoproduct f] (c : Cofan f)
  证明: (colimit.isColimit (Discrete.functor f)).nonempty_isColimit_iff_isIso_desc

@[deprecated (since := "2026-01-21")]
alias Cofan.isColimit_iff_isIso_sigmaDesc := Cofan.nonempty_isColimit_iff_isIso_sigmaDesc

Depends on / 依赖: Discrete, Discrete.functor, colimit, colimit.isColimit, functor, isColimit, nonempty_isColimit_iff_isIso_desc
-/
lemma Cofan.nonempty_isColimit_iff_isIso_sigmaDesc {f : β -> C} [HasCoproduct f] (c : Cofan f) :
    Nonempty (IsColimit c) ↔ IsIso (Sigma.desc c.inj) :=
  (colimit.isColimit (Discrete.functor f)).nonempty_isColimit_iff_isIso_desc

@[deprecated (since := "2026-01-21")]
alias Cofan.isColimit_iff_isIso_sigmaDesc := Cofan.nonempty_isColimit_iff_isIso_sigmaDesc

/--
Definition of `Cofan.isColimitTrans` / `Cofan.isColimitTrans` 的定义

English:
definition Cofan.isColimitTrans
  signature: {X : α -> C} (c : Cofan X) (hc : IsColimit c)
  body: by
  refine Cofan.IsColimit.mk _ ?_ ?_ ?_
  · exact fun t => hc.desc (Cofan.mk _ fun a => (hs a).desc (Cofan.mk t.pt (fun b => t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    refine hc.hom_ext fun ⟨a⟩ => (hs a).hom_ext fun ⟨b⟩ => ?_
    erw [hc.fac, (hs a).fac]
    simpa using! h ⟨a, b⟩

中文:
定义 Cofan.isColimitTrans
  签名: {X : α -> C} (c : Cofan X) (hc : 是余极限 c)
  定义体: by
  refine Cofan.IsColimit.mk _ ?_ ?_ ?_
  · exact fun t => hc.desc (Cofan.mk _ fun a => (hs a).desc (Cofan.mk t.pt (fun b => t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    refine hc.hom_ext fun ⟨a⟩ => (hs a).hom_ext fun ⟨b⟩ => ?_
    erw [hc.fac, (hs a).fac]
    simpa using! h ⟨a, b⟩

Depends on / 依赖: c.pt
-/
def Cofan.isColimitTrans {X : α -> C} (c : Cofan X) (hc : IsColimit c)
    {β : α -> Type*} {Y : (a : α) -> β a -> C} (π : (a : α) -> (b : β a) -> Y a b ⟶ X a)
      (hs : forall a, IsColimit (Cofan.mk (X a) (π a))) :
        IsColimit (Cofan.mk (f := fun ⟨a,b⟩ => Y a b) c.pt
          (fun (⟨a, b⟩ : Σ a, _) => π a b ≫ c.inj a)) := by
  refine Cofan.IsColimit.mk _ ?_ ?_ ?_
  · exact fun t => hc.desc (Cofan.mk _ fun a => (hs a).desc (Cofan.mk t.pt (fun b => t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    refine hc.hom_ext fun ⟨a⟩ => (hs a).hom_ext fun ⟨b⟩ => ?_
    erw [hc.fac, (hs a).fac]
    simpa using! h ⟨a, b⟩

/--
Definition of `Pi.map` / `Pi.map` 的定义

English:
definition Pi.map
  signature: {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b)
  body: limMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp), elementwise nosimp]

中文:
定义 依赖函数类型.map
  签名: {f g : β -> C} [HasProduct f] [HasProduct g] (p : 对任意 b, f b ⟶ g b)
  定义体: limMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp), elementwise nosimp]

Depends on / 依赖: Discrete, Discrete.natTrans, X.as, limMap, natTrans
-/
def Pi.map {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  limMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp), elementwise nosimp]
/--
lemma `Pi.map_π` / 引理 `Pi.map_π`

English:
lemma Pi.map_π
  given: {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b) (b : β)
  proof: by simp [Pi.map]

@[simp]

中文:
引理 依赖函数类型.map_π
  条件: {f g : β -> C} [HasProduct f] [HasProduct g] (p : 对任意 b, f b ⟶ g b) (b : β)
  证明: by simp [Pi.map]

@[simp]

Depends on / 依赖: Pi.map
-/
lemma Pi.map_π {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b) (b : β) :
    Pi.map p ≫ Pi.π g b = Pi.π f b ≫ p b := by simp [Pi.map]

@[simp]
/--
lemma `Pi.map_id` / 引理 `Pi.map_id`

English:
lemma Pi.map_id
  given: {f : α -> C} [HasProduct f]
  statement: Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f)
  proof: by
  ext; simp

中文:
引理 依赖函数类型.map_id
  条件: {f : α -> C} [HasProduct f]
  结论: 依赖函数类型.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f)
  证明: by
  ext; simp
-/
lemma Pi.map_id {f : α -> C} [HasProduct f] : Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

/--
lemma `Pi.map_comp_map` / 引理 `Pi.map_comp_map`

English:
lemma Pi.map_comp_map
  statement: {f g h : α -> C} [HasProduct f] [HasProduct g] [HasProduct h]
  proof: by
  ext; simp

中文:
引理 依赖函数类型.map_comp_map
  结论: {f g h : α -> C} [HasProduct f] [HasProduct g] [HasProduct h]
  证明: by
  ext; simp
-/
lemma Pi.map_comp_map {f g h : α -> C} [HasProduct f] [HasProduct g] [HasProduct h]
    (q : forall (a : α), f a ⟶ g a) (q' : forall (a : α), g a ⟶ h a) :
    Pi.map q ≫ Pi.map q' = Pi.map (fun a => q a ≫ q' a) := by
  ext; simp

/--
Instance `Pi.map_mono` / 实例 `Pi.map_mono`

English:
instance Pi.map_mono
  signature: {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b)
  body: @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

中文:
实例 依赖函数类型.map_mono
  签名: {f g : β -> C} [HasProduct f] [HasProduct g] (p : 对任意 b, f b ⟶ g b)
  定义体: @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natTrans, Limits, Limits.limMap_mono, X.as, functor, infer_instance, limMap_mono, natTrans
-/
instance Pi.map_mono {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b)
[forall i, Mono (p i)] : Mono Pi.map p :=
  @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/--
Definition of `Pi.map'` / `Pi.map'` 的定义

English:
definition Pi.map'
  signature: {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] (p : β -> α)
  body: Pi.lift (fun a => Pi.π _ _ ≫ q a)

@[reassoc (attr := simp)]

中文:
定义 依赖函数类型.map'
  签名: {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] (p : β -> α)
  定义体: Pi.lift (fun a => Pi.π _ _ ≫ q a)

@[reassoc (attr := simp)]

Depends on / 依赖: Pi.lift
-/
def Pi.map' {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] (p : β -> α)
    (q : forall (b : β), f (p b) ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  Pi.lift (fun a => Pi.π _ _ ≫ q a)

@[reassoc (attr := simp)]
/--
lemma `Pi.map'_comp_π` / 引理 `Pi.map'_comp_π`

English:
lemma Pi.map'_comp_π
  statement: {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] (p : β -> α)
  proof: limit.lift_π _ _

中文:
引理 依赖函数类型.map'_comp_π
  结论: {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] (p : β -> α)
  证明: limit.lift_π _ _
-/
lemma Pi.map'_comp_π {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] (p : β -> α)
    (q : forall (b : β), f (p b) ⟶ g b) (b : β) : Pi.map' p q ≫ Pi.π g b = Pi.π f (p b) ≫ q b :=
  limit.lift_π _ _

/--
lemma `Pi.map'_id_id` / 引理 `Pi.map'_id_id`

English:
lemma Pi.map'_id_id
  given: {f : α -> C} [HasProduct f]
  statement: Pi.map' id (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f)
  proof: by
  ext; simp

@[simp]

中文:
引理 依赖函数类型.map'_id_id
  条件: {f : α -> C} [HasProduct f]
  结论: 依赖函数类型.map' id (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f)
  证明: by
  ext; simp

@[simp]
-/
lemma Pi.map'_id_id {f : α -> C} [HasProduct f] : Pi.map' id (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

@[simp]
/--
lemma `Pi.map'_id` / 引理 `Pi.map'_id`

English:
lemma Pi.map'_id
  given: {f g : α -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b)
  proof: rfl

中文:
引理 依赖函数类型.map'_id
  条件: {f g : α -> C} [HasProduct f] [HasProduct g] (p : 对任意 b, f b ⟶ g b)
  证明: rfl
-/
lemma Pi.map'_id {f g : α -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g b) :
    Pi.map' id p = Pi.map p :=
  rfl

/--
lemma `Pi.map'_comp_map'` / 引理 `Pi.map'_comp_map'`

English:
lemma Pi.map'_comp_map'
  statement: {f : α -> C} {g : β -> C} {h : γ -> C} [HasProduct f] [HasProduct g]
  proof: by
  ext; simp

中文:
引理 依赖函数类型.map'_comp_map'
  结论: {f : α -> C} {g : β -> C} {h : γ -> C} [HasProduct f] [HasProduct g]
  证明: by
  ext; simp
-/
lemma Pi.map'_comp_map' {f : α -> C} {g : β -> C} {h : γ -> C} [HasProduct f] [HasProduct g]
    [HasProduct h] (p : β -> α) (p' : γ -> β) (q : forall (b : β), f (p b) ⟶ g b)
    (q' : forall (c : γ), g (p' c) ⟶ h c) :
    Pi.map' p q ≫ Pi.map' p' q' = Pi.map' (p ∘ p') (fun c => q (p' c) ≫ q' c) := by
  ext; simp

/--
lemma `Pi.map'_comp_map` / 引理 `Pi.map'_comp_map`

English:
lemma Pi.map'_comp_map
  statement: {f : α -> C} {g h : β -> C} [HasProduct f] [HasProduct g] [HasProduct h]
  proof: by
  ext; simp

中文:
引理 依赖函数类型.map'_comp_map
  结论: {f : α -> C} {g h : β -> C} [HasProduct f] [HasProduct g] [HasProduct h]
  证明: by
  ext; simp
-/
lemma Pi.map'_comp_map {f : α -> C} {g h : β -> C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β -> α) (q : forall (b : β), f (p b) ⟶ g b) (q' : forall (b : β), g b ⟶ h b) :
    Pi.map' p q ≫ Pi.map q' = Pi.map' p (fun b => q b ≫ q' b) := by
  ext; simp

/--
lemma `Pi.map_comp_map'` / 引理 `Pi.map_comp_map'`

English:
lemma Pi.map_comp_map'
  statement: {f g : α -> C} {h : β -> C} [HasProduct f] [HasProduct g] [HasProduct h]
  proof: by
  ext; simp

中文:
引理 依赖函数类型.map_comp_map'
  结论: {f g : α -> C} {h : β -> C} [HasProduct f] [HasProduct g] [HasProduct h]
  证明: by
  ext; simp
-/
lemma Pi.map_comp_map' {f g : α -> C} {h : β -> C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β -> α) (q : forall (a : α), f a ⟶ g a) (q' : forall (b : β), g (p b) ⟶ h b) :
    Pi.map q ≫ Pi.map' p q' = Pi.map' p (fun b => q (p b) ≫ q' b) := by
  ext; simp

/--
lemma `Pi.map'_eq` / 引理 `Pi.map'_eq`

English:
lemma Pi.map'_eq
  statement: {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] {p p' : β -> α}
  proof: by
  cat_disch

中文:
引理 依赖函数类型.map'_eq
  结论: {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] {p p' : β -> α}
  证明: by
  cat_disch
-/
lemma Pi.map'_eq {f : α -> C} {g : β -> C} [HasProduct f] [HasProduct g] {p p' : β -> α}
    {q : forall (b : β), f (p b) ⟶ g b} {q' : forall (b : β), f (p' b) ⟶ g b} (hp : p = p')
    (hq : forall (b : β), eqToHom (hp ▸ rfl) ≫ q b = q' b) : Pi.map' p q = Pi.map' p' q' := by
  cat_disch

/--
Definition of `Pi.mapIso` / `Pi.mapIso` 的定义

English:
definition Pi.mapIso
  signature: {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ≅ g b)
  body: lim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]

中文:
定义 依赖函数类型.mapIso
  签名: {f g : β -> C} [HasProductsOfShape β C] (p : 对任意 b, f b ≅ g b)
  定义体: lim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.natIso, X.as, lim.mapIso, mapIso, natIso
-/
def Pi.mapIso {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ≅ g b) : ∏ᶜ f ≅ ∏ᶜ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]
/--
lemma `Pi.mapIso_hom_π` / 引理 `Pi.mapIso_hom_π`

English:
lemma Pi.mapIso_hom_π
  given: {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ≅ g b) (b : β)
  proof: limMap_π _ _

@[reassoc (attr := simp)]

中文:
引理 依赖函数类型.mapIso_hom_π
  条件: {f g : β -> C} [HasProductsOfShape β C] (p : 对任意 b, f b ≅ g b) (b : β)
  证明: limMap_π _ _

@[reassoc (attr := simp)]
-/
lemma Pi.mapIso_hom_π {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).hom ≫ π _ _ = π _ _ ≫ (p b).hom :=
  limMap_π _ _

@[reassoc (attr := simp)]
/--
lemma `Pi.mapIso_inv_π` / 引理 `Pi.mapIso_inv_π`

English:
lemma Pi.mapIso_inv_π
  given: {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ≅ g b) (b : β)
  proof: limMap_π _ _

中文:
引理 依赖函数类型.mapIso_inv_π
  条件: {f g : β -> C} [HasProductsOfShape β C] (p : 对任意 b, f b ≅ g b) (b : β)
  证明: limMap_π _ _
-/
lemma Pi.mapIso_inv_π {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).inv ≫ π _ _ = π _ _ ≫ (p b).inv :=
  limMap_π _ _

/--
Instance `Pi.map_isIso` / 实例 `Pi.map_isIso`

English:
instance Pi.map_isIso
  signature: {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ⟶ g b)
  body: inferInstanceAs (IsIso (Pi.mapIso (fun b => asIso (p b))).hom)

中文:
实例 依赖函数类型.map_isIso
  签名: {f g : β -> C} [HasProductsOfShape β C] (p : 对任意 b, f b ⟶ g b)
  定义体: inferInstanceAs (IsIso (Pi.mapIso (fun b => asIso (p b))).hom)

Depends on / 依赖: Pi.mapIso, mapIso
-/
instance Pi.map_isIso {f g : β -> C} [HasProductsOfShape β C] (p : forall b, f b ⟶ g b)
[forall b, IsIso <| p b] : IsIso Pi.map p :=
  inferInstanceAs (IsIso (Pi.mapIso (fun b => asIso (p b))).hom)

section

/- In this section, we provide some API for products when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasProduct (fun j => X.obj (Discrete.mk j))]

/-- A limit cone for `X : Discrete α ⥤ C` that is given
by `∏ᶜ (fun j => X.obj (Discrete.mk j))`. -/
@[simps]
/--
Definition of `Pi.cone` / `Pi.cone` 的定义

English:
definition Pi.cone
  signature: : Cone X where
  body: ∏ᶜ (fun j => X.obj (Discrete.mk j))
  π := Discrete.natTrans (fun _ => Pi.π _ _)

中文:
定义 依赖函数类型.cone
  签名: : 锥 X where
  定义体: ∏ᶜ (fun j => X.obj (Discrete.mk j))
  π := Discrete.natTrans (fun _ => Pi.π _ _)

Depends on / 依赖: Discrete, Discrete.mk, X.obj
-/
def Pi.cone : Cone X where
  pt := ∏ᶜ (fun j => X.obj (Discrete.mk j))
  π := Discrete.natTrans (fun _ => Pi.π _ _)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `productIsProduct'` / `productIsProduct'` 的定义

English:
definition productIsProduct'
  signature: :
  body: Pi.lift (fun j => s.π.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply hm

中文:
定义 productIsProduct'
  签名: :
  定义体: Pi.lift (fun j => s.π.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply hm

Depends on / 依赖: Pi.lift
-/
def productIsProduct' :
    IsLimit (Pi.cone X) where
  lift s := Pi.lift (fun j => s.π.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply hm

variable [HasLimit X]

/--
Definition of `Pi.isoLimit` / `Pi.isoLimit` 的定义

English:
definition Pi.isoLimit
  signature: :
  body: IsLimit.conePointUniqueUpToIso (productIsProduct' X) (limit.isLimit X)

@[reassoc (attr := simp)]

中文:
定义 依赖函数类型.isoLimit
  签名: :
  定义体: IsLimit.conePointUniqueUpToIso (productIsProduct' X) (limit.isLimit X)

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit, productIsProduct
-/
def Pi.isoLimit :
    ∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X :=
  IsLimit.conePointUniqueUpToIso (productIsProduct' X) (limit.isLimit X)

@[reassoc (attr := simp)]
/--
lemma `Pi.isoLimit_inv_π` / 引理 `Pi.isoLimit_inv_π`

English:
lemma Pi.isoLimit_inv_π
  given: (j : α)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[reassoc (attr := simp)]

中文:
引理 依赖函数类型.isoLimit_inv_π
  条件: (j : α)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
lemma Pi.isoLimit_inv_π (j : α) :
    (Pi.isoLimit X).inv ≫ Pi.π _ j = limit.π _ (Discrete.mk j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[reassoc (attr := simp)]
/--
lemma `Pi.isoLimit_hom_π` / 引理 `Pi.isoLimit_hom_π`

English:
lemma Pi.isoLimit_hom_π
  given: (j : α)
  proof: IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

中文:
引理 依赖函数类型.isoLimit_hom_π
  条件: (j : α)
  证明: IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, conePointUniqueUpToIso_hom_comp
-/
lemma Pi.isoLimit_hom_π (j : α) :
    (Pi.isoLimit X).hom ≫ limit.π _ (Discrete.mk j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

end

/--
Definition of `Sigma.map` / `Sigma.map` 的定义

English:
definition Sigma.map
  signature: {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b)
  body: colimMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp)]

中文:
定义 依赖和类型.map
  签名: {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : 对任意 b, f b ⟶ g b)
  定义体: colimMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.natTrans, X.as, colimMap, natTrans
-/
def Sigma.map {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b) :
    ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp)]
/--
lemma `Sigma.ι_map` / 引理 `Sigma.ι_map`

English:
lemma Sigma.ι_map
  given: {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b) (b : β)
  proof: by simp [Sigma.map]

@[simp]

中文:
引理 依赖和类型.ι_map
  条件: {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : 对任意 b, f b ⟶ g b) (b : β)
  证明: by simp [Sigma.map]

@[simp]

Depends on / 依赖: Sigma.map
-/
lemma Sigma.ι_map {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b) (b : β) :
    Sigma.ι f b ≫ Sigma.map p = p b ≫ Sigma.ι g b := by simp [Sigma.map]

@[simp]
/--
lemma `Sigma.map_id` / 引理 `Sigma.map_id`

English:
lemma Sigma.map_id
  given: {f : α -> C} [HasCoproduct f]
  statement: Sigma.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f)
  proof: by
  ext; simp

中文:
引理 依赖和类型.map_id
  条件: {f : α -> C} [HasCoproduct f]
  结论: 依赖和类型.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f)
  证明: by
  ext; simp
-/
lemma Sigma.map_id {f : α -> C} [HasCoproduct f] : Sigma.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp

/--
lemma `Sigma.map_comp_map` / 引理 `Sigma.map_comp_map`

English:
lemma Sigma.map_comp_map
  statement: {f g h : α -> C} [HasCoproduct f] [HasCoproduct g] [HasCoproduct h]
  proof: by
  ext; simp

中文:
引理 依赖和类型.map_comp_map
  结论: {f g h : α -> C} [HasCoproduct f] [HasCoproduct g] [HasCoproduct h]
  证明: by
  ext; simp
-/
lemma Sigma.map_comp_map {f g h : α -> C} [HasCoproduct f] [HasCoproduct g] [HasCoproduct h]
    (q : forall (a : α), f a ⟶ g a) (q' : forall (a : α), g a ⟶ h a) :
    Sigma.map q ≫ Sigma.map q' = Sigma.map (fun a => q a ≫ q' a) := by
  ext; simp

/--
Instance `Sigma.map_epi` / 实例 `Sigma.map_epi`

English:
instance Sigma.map_epi
  signature: {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b)
  body: @Limits.colimMap_epi _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

中文:
实例 依赖和类型.map_epi
  签名: {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : 对任意 b, f b ⟶ g b)
  定义体: @Limits.colimMap_epi _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natTrans, Limits, Limits.colimMap_epi, X.as, colimMap_epi, functor, infer_instance, natTrans
-/
instance Sigma.map_epi {f g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b)
[forall i, Epi (p i)] : Epi Sigma.map p :=
  @Limits.colimMap_epi _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/--
Definition of `Sigma.map'` / `Sigma.map'` 的定义

English:
definition Sigma.map'
  signature: {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : α -> β)
  body: Sigma.desc (fun a => q a ≫ Sigma.ι _ _)

@[reassoc (attr := simp)]

中文:
定义 依赖和类型.map'
  签名: {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : α -> β)
  定义体: Sigma.desc (fun a => q a ≫ Sigma.ι _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: Sigma.desc
-/
def Sigma.map' {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g] (p : α -> β)
    (q : forall (a : α), f a ⟶ g (p a)) : ∐ f ⟶ ∐ g :=
  Sigma.desc (fun a => q a ≫ Sigma.ι _ _)

@[reassoc (attr := simp)]
/--
lemma `Sigma.ι_comp_map'` / 引理 `Sigma.ι_comp_map'`

English:
lemma Sigma.ι_comp_map'
  statement: {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g]
  proof: colimit.ι_desc _ _

中文:
引理 依赖和类型.ι_comp_map'
  结论: {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g]
  证明: colimit.ι_desc _ _

Depends on / 依赖: RespectsLeft, RespectsLeft.precomp, colimit, f.unop, i.unop, precomp
-/
lemma Sigma.ι_comp_map' {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g]
    (p : α -> β) (q : forall (a : α), f a ⟶ g (p a)) (a : α) :
    Sigma.ι f a ≫ Sigma.map' p q = q a ≫ Sigma.ι g (p a) :=
  colimit.ι_desc _ _

/--
lemma `Sigma.map'_id_id` / 引理 `Sigma.map'_id_id`

English:
lemma Sigma.map'_id_id
  given: {f : α -> C} [HasCoproduct f]
  proof: by
  ext; simp

@[simp]

中文:
引理 依赖和类型.map'_id_id
  条件: {f : α -> C} [HasCoproduct f]
  证明: by
  ext; simp

@[simp]

Depends on / 依赖: RespectsRight, RespectsRight.postcomp, f.unop, i.unop, postcomp
-/
lemma Sigma.map'_id_id {f : α -> C} [HasCoproduct f] :
    Sigma.map' id (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp

@[simp]
/--
lemma `Sigma.map'_id` / 引理 `Sigma.map'_id`

English:
lemma Sigma.map'_id
  given: {f g : α -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b)
  proof: rfl

中文:
引理 依赖和类型.map'_id
  条件: {f g : α -> C} [HasCoproduct f] [HasCoproduct g] (p : 对任意 b, f b ⟶ g b)
  证明: rfl
-/
lemma Sigma.map'_id {f g : α -> C} [HasCoproduct f] [HasCoproduct g] (p : forall b, f b ⟶ g b) :
    Sigma.map' id p = Sigma.map p :=
  rfl

/--
lemma `Sigma.map'_comp_map'` / 引理 `Sigma.map'_comp_map'`

English:
lemma Sigma.map'_comp_map'
  statement: {f : α -> C} {g : β -> C} {h : γ -> C} [HasCoproduct f] [HasCoproduct g]
  proof: by
  ext; simp

中文:
引理 依赖和类型.map'_comp_map'
  结论: {f : α -> C} {g : β -> C} {h : γ -> C} [HasCoproduct f] [HasCoproduct g]
  证明: by
  ext; simp
-/
lemma Sigma.map'_comp_map' {f : α -> C} {g : β -> C} {h : γ -> C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α -> β) (p' : β -> γ) (q : forall (a : α), f a ⟶ g (p a))
    (q' : forall (b : β), g b ⟶ h (p' b)) :
    Sigma.map' p q ≫ Sigma.map' p' q' = Sigma.map' (p' ∘ p) (fun a => q a ≫ q' (p a)) := by
  ext; simp

/--
lemma `Sigma.map'_comp_map` / 引理 `Sigma.map'_comp_map`

English:
lemma Sigma.map'_comp_map
  statement: {f : α -> C} {g h : β -> C} [HasCoproduct f] [HasCoproduct g]
  proof: by
  ext; simp

中文:
引理 依赖和类型.map'_comp_map
  结论: {f : α -> C} {g h : β -> C} [HasCoproduct f] [HasCoproduct g]
  证明: by
  ext; simp
-/
lemma Sigma.map'_comp_map {f : α -> C} {g h : β -> C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α -> β) (q : forall (a : α), f a ⟶ g (p a)) (q' : forall (b : β), g b ⟶ h b) :
    Sigma.map' p q ≫ Sigma.map q' = Sigma.map' p (fun a => q a ≫ q' (p a)) := by
  ext; simp

/--
lemma `Sigma.map_comp_map'` / 引理 `Sigma.map_comp_map'`

English:
lemma Sigma.map_comp_map'
  statement: {f g : α -> C} {h : β -> C} [HasCoproduct f] [HasCoproduct g]
  proof: by
  ext; simp

中文:
引理 依赖和类型.map_comp_map'
  结论: {f g : α -> C} {h : β -> C} [HasCoproduct f] [HasCoproduct g]
  证明: by
  ext; simp
-/
lemma Sigma.map_comp_map' {f g : α -> C} {h : β -> C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α -> β) (q : forall (a : α), f a ⟶ g a) (q' : forall (a : α), g a ⟶ h (p a)) :
    Sigma.map q ≫ Sigma.map' p q' = Sigma.map' p (fun a => q a ≫ q' a) := by
  ext; simp

/--
lemma `Sigma.map'_eq` / 引理 `Sigma.map'_eq`

English:
lemma Sigma.map'_eq
  statement: {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g]
  proof: by
  cat_disch

中文:
引理 依赖和类型.map'_eq
  结论: {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g]
  证明: by
  cat_disch
-/
lemma Sigma.map'_eq {f : α -> C} {g : β -> C} [HasCoproduct f] [HasCoproduct g]
    {p p' : α -> β} {q : forall (a : α), f a ⟶ g (p a)} {q' : forall (a : α), f a ⟶ g (p' a)}
    (hp : p = p') (hq : forall (a : α), q a ≫ eqToHom (hp ▸ rfl) = q' a) :
    Sigma.map' p q = Sigma.map' p' q' := by
  cat_disch

/--
Definition of `Sigma.mapIso` / `Sigma.mapIso` 的定义

English:
definition Sigma.mapIso
  signature: {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ≅ g b)
  body: colim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]

中文:
定义 依赖和类型.mapIso
  签名: {f g : β -> C} [HasCoproductsOfShape β C] (p : 对任意 b, f b ≅ g b)
  定义体: colim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.natIso, X.as, colim.mapIso, mapIso, natIso
-/
def Sigma.mapIso {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]
/--
lemma `Sigma.ι_mapIso_hom` / 引理 `Sigma.ι_mapIso_hom`

English:
lemma Sigma.ι_mapIso_hom
  given: {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ≅ g b) (b : β)
  proof: ι_colimMap _ _

@[reassoc (attr := simp)]

中文:
引理 依赖和类型.ι_mapIso_hom
  条件: {f g : β -> C} [HasCoproductsOfShape β C] (p : 对任意 b, f b ≅ g b) (b : β)
  证明: ι_colimMap _ _

@[reassoc (attr := simp)]
-/
lemma Sigma.ι_mapIso_hom {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ≅ g b) (b : β) :
    ι _ _ ≫ (Sigma.mapIso p).hom = (p b).hom ≫ ι _ _ :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
/--
lemma `Sigma.ι_mapIso_inv` / 引理 `Sigma.ι_mapIso_inv`

English:
lemma Sigma.ι_mapIso_inv
  given: {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ≅ g b) (b : β)
  proof: ι_colimMap _ _

中文:
引理 依赖和类型.ι_mapIso_inv
  条件: {f g : β -> C} [HasCoproductsOfShape β C] (p : 对任意 b, f b ≅ g b) (b : β)
  证明: ι_colimMap _ _
-/
lemma Sigma.ι_mapIso_inv {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ≅ g b) (b : β) :
    ι _ _ ≫ (Sigma.mapIso p).inv = (p b).inv ≫ ι _ _ :=
  ι_colimMap _ _

/--
Instance `Sigma.map_isIso` / 实例 `Sigma.map_isIso`

English:
instance Sigma.map_isIso
  signature: {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ⟶ g b)
  body: inferInstanceAs (IsIso (Sigma.mapIso (fun b => asIso (p b))).hom)

中文:
实例 依赖和类型.map_isIso
  签名: {f g : β -> C} [HasCoproductsOfShape β C] (p : 对任意 b, f b ⟶ g b)
  定义体: inferInstanceAs (IsIso (Sigma.mapIso (fun b => asIso (p b))).hom)

Depends on / 依赖: Sigma.mapIso, mapIso
-/
instance Sigma.map_isIso {f g : β -> C} [HasCoproductsOfShape β C] (p : forall b, f b ⟶ g b)
    [forall b, IsIso <| p b] : IsIso (Sigma.map p) :=
  inferInstanceAs (IsIso (Sigma.mapIso (fun b => asIso (p b))).hom)

section

/- In this section, we provide some API for coproducts when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasCoproduct (fun j => X.obj (Discrete.mk j))]

/-- A colimit cocone for `X : Discrete α ⥤ C` that is given
by `∐ (fun j => X.obj (Discrete.mk j))`. -/
@[simps]
/--
Definition of `Sigma.cocone` / `Sigma.cocone` 的定义

English:
definition Sigma.cocone
  signature: : Cocone X where
  body: ∐ (fun j => X.obj (Discrete.mk j))
  ι := Discrete.natTrans (fun _ => Sigma.ι (fun j => X.obj ⟨j⟩) _)

中文:
定义 依赖和类型.cocone
  签名: : 余锥 X where
  定义体: ∐ (fun j => X.obj (Discrete.mk j))
  ι := Discrete.natTrans (fun _ => Sigma.ι (fun j => X.obj ⟨j⟩) _)

Depends on / 依赖: Discrete, Discrete.mk, X.obj
-/
def Sigma.cocone : Cocone X where
  pt := ∐ (fun j => X.obj (Discrete.mk j))
  ι := Discrete.natTrans (fun _ => Sigma.ι (fun j => X.obj ⟨j⟩) _)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `coproductIsCoproduct'` / `coproductIsCoproduct'` 的定义

English:
definition coproductIsCoproduct'
  signature: :
  body: Sigma.desc (fun j => s.ι.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    apply hm

中文:
定义 coproductIsCoproduct'
  签名: :
  定义体: Sigma.desc (fun j => s.ι.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    apply hm

Depends on / 依赖: Sigma.desc
-/
def coproductIsCoproduct' :
    IsColimit (Sigma.cocone X) where
  desc s := Sigma.desc (fun j => s.ι.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    apply hm

variable [HasColimit X]

/--
Definition of `Sigma.isoColimit` / `Sigma.isoColimit` 的定义

English:
definition Sigma.isoColimit
  signature: :
  body: IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct' X) (colimit.isColimit X)

@[reassoc (attr := simp)]

中文:
定义 依赖和类型.isoColimit
  签名: :
  定义体: IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct' X) (colimit.isColimit X)

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, coproductIsCoproduct, isColimit
-/
def Sigma.isoColimit :
    ∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct' X) (colimit.isColimit X)

@[reassoc (attr := simp)]
/--
lemma `Sigma.ι_isoColimit_hom` / 引理 `Sigma.ι_isoColimit_hom`

English:
lemma Sigma.ι_isoColimit_hom
  given: (j : α)
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct' X) _ _

@[reassoc (attr := simp)]

中文:
引理 依赖和类型.ι_isoColimit_hom
  条件: (j : α)
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct' X) _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom, coproductIsCoproduct
-/
lemma Sigma.ι_isoColimit_hom (j : α) :
    Sigma.ι _ j ≫ (Sigma.isoColimit X).hom = colimit.ι _ (Discrete.mk j) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct' X) _ _

@[reassoc (attr := simp)]
/--
lemma `Sigma.ι_isoColimit_inv` / 引理 `Sigma.ι_isoColimit_inv`

English:
lemma Sigma.ι_isoColimit_inv
  given: (j : α)
  proof: IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

中文:
引理 依赖和类型.ι_isoColimit_inv
  条件: (j : α)
  证明: IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, comp_coconePointUniqueUpToIso_inv
-/
lemma Sigma.ι_isoColimit_inv (j : α) :
    colimit.ι _ ⟨j⟩ ≫ (Sigma.isoColimit X).inv = Sigma.ι (fun j => X.obj ⟨j⟩) _ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

end

/-- Two products which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
/--
Definition of `Pi.whiskerEquiv` / `Pi.whiskerEquiv` 的定义

English:
definition Pi.whiskerEquiv
  signature: {J K : Type*} {f : J -> C} {g : K -> C} (e : J ≃ K) (w : forall j, g (e j) ≅ f j)
  body: Pi.map' e.symm fun k => (w (e.symm k)).inv ≫ eqToHom (by simp)
  inv := Pi.map' e fun j => (w j).hom

中文:
定义 依赖函数类型.whiskerEquiv
  签名: {J K : 类型} {f : J -> C} {g : K -> C} (e : J ≃ K) (w : 对任意 j, g (e j) ≅ f j)
  定义体: Pi.map' e.symm fun k => (w (e.symm k)).inv ≫ eqToHom (by simp)
  inv := Pi.map' e fun j => (w j).hom

Depends on / 依赖: Pi.map, e.symm, eqToHom
-/
def Pi.whiskerEquiv {J K : Type*} {f : J -> C} {g : K -> C} (e : J ≃ K) (w : forall j, g (e j) ≅ f j)
    [HasProduct f] [HasProduct g] : ∏ᶜ f ≅ ∏ᶜ g where
  hom := Pi.map' e.symm fun k => (w (e.symm k)).inv ≫ eqToHom (by simp)
  inv := Pi.map' e fun j => (w j).hom

/-- Two coproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
/--
Definition of `Sigma.whiskerEquiv` / `Sigma.whiskerEquiv` 的定义

English:
definition Sigma.whiskerEquiv
  signature: {J K : Type*} {f : J -> C} {g : K -> C} (e : J ≃ K) (w : forall j, g (e j) ≅ f j)
  body: Sigma.map' e fun j => (w j).inv
  inv := Sigma.map' e.symm fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom

中文:
定义 依赖和类型.whiskerEquiv
  签名: {J K : 类型} {f : J -> C} {g : K -> C} (e : J ≃ K) (w : 对任意 j, g (e j) ≅ f j)
  定义体: Sigma.map' e fun j => (w j).inv
  inv := Sigma.map' e.symm fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom

Depends on / 依赖: Sigma.map
-/
def Sigma.whiskerEquiv {J K : Type*} {f : J -> C} {g : K -> C} (e : J ≃ K) (w : forall j, g (e j) ≅ f j)
    [HasCoproduct f] [HasCoproduct g] : ∐ f ≅ ∐ g where
  hom := Sigma.map' e fun j => (w j).inv
  inv := Sigma.map' e.symm fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom

instance {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
    [forall i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    HasProduct fun p : Σ i, f i => g p.1 p.2 where
  exists_limit := Nonempty.intro
    { cone := Fan.mk (∏ᶜ fun i => ∏ᶜ g i) (fun X => Pi.π (fun i => ∏ᶜ g i) X.1 ≫ Pi.π (g X.1) X.2)
      isLimit := Fan.IsLimit.mk _ (fun s => Pi.lift fun b => Pi.lift fun c => s.proj ⟨b, c⟩)
        (by simp)
        (by intro s (m : _ ⟶ (∏ᶜ fun i => ∏ᶜ g i)) w; aesop (add norm simp Sigma.forall)) }

/-- An iterated product is a product over a sigma type. -/
@[simps]
/--
Definition of `piPiIso` / `piPiIso` 的定义

English:
definition piPiIso
  signature: {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
  body: Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

中文:
定义 piPiIso
  签名: {ι : 类型} (f : ι -> 类型) (g : (i : ι) -> (f i) -> C)
  定义体: Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

Depends on / 依赖: Pi.lift
-/
def piPiIso {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
    [forall i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    (∏ᶜ fun i => ∏ᶜ g i) ≅ (∏ᶜ fun p : Σ i, f i => g p.1 p.2) where
  hom := Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)

instance {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
    [forall i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    HasCoproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_colimit := Nonempty.intro
    { cocone := Cofan.mk (∐ fun i => ∐ g i)
        (fun X => Sigma.ι (g X.1) X.2 ≫ Sigma.ι (fun i => ∐ g i) X.1)
      isColimit := Cofan.IsColimit.mk _
        (fun s => Sigma.desc fun b => Sigma.desc fun c => s.inj ⟨b, c⟩)
        (by simp)
        (by intro s (m : (∐ fun i => ∐ g i) ⟶ _) w; aesop_cat (add norm simp Sigma.forall)) }

/-- An iterated coproduct is a coproduct over a sigma type. -/
@[simps]
/--
Definition of `sigmaSigmaIso` / `sigmaSigmaIso` 的定义

English:
definition sigmaSigmaIso
  signature: {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
  body: Sigma.desc fun i => Sigma.desc fun x => Sigma.ι (fun p : Σ i, f i => g p.1 p.2) ⟨i, x⟩
  inv := Sigma.desc fun ⟨i, x⟩ => Sigma.ι (g i) x ≫ Sigma.ι (fun i => ∐ g i) i

中文:
定义 sigmaSigmaIso
  签名: {ι : 类型} (f : ι -> 类型) (g : (i : ι) -> (f i) -> C)
  定义体: Sigma.desc fun i => Sigma.desc fun x => Sigma.ι (fun p : Σ i, f i => g p.1 p.2) ⟨i, x⟩
  inv := Sigma.desc fun ⟨i, x⟩ => Sigma.ι (g i) x ≫ Sigma.ι (fun i => ∐ g i) i

Depends on / 依赖: Sigma.desc
-/
def sigmaSigmaIso {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C)
    [forall i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    (∐ fun i => ∐ g i) ≅ (∐ fun p : Σ i, f i => g p.1 p.2) where
  hom := Sigma.desc fun i => Sigma.desc fun x => Sigma.ι (fun p : Σ i, f i => g p.1 p.2) ⟨i, x⟩
  inv := Sigma.desc fun ⟨i, x⟩ => Sigma.ι (g i) x ≫ Sigma.ι (fun i => ∐ g i) i

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
variable (f : β -> C)

/--
Definition of `piComparison` / `piComparison` 的定义

English:
definition piComparison
  signature: [HasProduct f] [HasProduct fun b => G.obj (f b)]
  body: Pi.lift fun b => G.map (Pi.π f b)

@[reassoc (attr := simp), elementwise nosimp]

中文:
定义 piComparison
  签名: [HasProduct f] [HasProduct fun b => G.obj (f b)]
  定义体: Pi.lift fun b => G.map (Pi.π f b)

@[reassoc (attr := simp), elementwise nosimp]

Depends on / 依赖: G.map, Pi.lift
-/
def piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] :
    G.obj (∏ᶜ f) ⟶ ∏ᶜ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)

@[reassoc (attr := simp), elementwise nosimp]
/--
theorem `piComparison_comp_π` / 定理 `piComparison_comp_π`

English:
theorem piComparison_comp_π
  given: [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β)
  proof: limit.lift_π _ (Discrete.mk b)

@[reassoc (attr := simp)]

中文:
定理 piComparison_comp_π
  条件: [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β)
  证明: limit.lift_π _ (Discrete.mk b)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.mk, limit.lift_
-/
theorem piComparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)

@[reassoc (attr := simp)]
/--
theorem `map_lift_piComparison` / 定理 `map_lift_piComparison`

English:
theorem map_lift_piComparison
  statement: [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
  proof: by
  ext j
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_π_app]

中文:
定理 map_lift_piComparison
  结论: [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
  证明: by
  ext j
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_π_app]

Depends on / 依赖: Category, Category.assoc, Fan.mk_, G.map_comp, limit.lift_, map_comp
-/
theorem map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
    (g : forall j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext j
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_π_app]

/--
Definition of `sigmaComparison` / `sigmaComparison` 的定义

English:
definition sigmaComparison
  signature: [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)]
  body: Sigma.desc fun b => G.map (Sigma.ι f b)

@[reassoc (attr := simp)]

中文:
定义 sigmaComparison
  签名: [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)]
  定义体: Sigma.desc fun b => G.map (Sigma.ι f b)

@[reassoc (attr := simp)]

Depends on / 依赖: G.map, Sigma.desc
-/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] :
    ∐ (fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)

@[reassoc (attr := simp)]
/--
theorem `ι_comp_sigmaComparison` / 定理 `ι_comp_sigmaComparison`

English:
theorem ι_comp_sigmaComparison
  given: [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β)
  proof: colimit.ι_desc _ (Discrete.mk b)

@[reassoc (attr := simp)]

中文:
定理 ι_comp_sigmaComparison
  条件: [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β)
  证明: colimit.ι_desc _ (Discrete.mk b)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.mk, colimit
-/
theorem ι_comp_sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ (Discrete.mk b)

@[reassoc (attr := simp)]
/--
theorem `sigmaComparison_map_desc` / 定理 `sigmaComparison_map_desc`

English:
theorem sigmaComparison_map_desc
  statement: [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
  proof: by
  ext j
  simp only [ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc, Cofan.mk_ι_app]

中文:
定理 sigmaComparison_map_desc
  结论: [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
  证明: by
  ext j
  simp only [ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc, Cofan.mk_ι_app]

Depends on / 依赖: Cofan.mk_, G.map_comp, colimit, map_comp
-/
theorem sigmaComparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
    (g : forall j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext j
  simp only [ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc, Cofan.mk_ι_app]

/--
Definition of `Fan.isLimitMapConeEquiv` / `Fan.isLimitMapConeEquiv` 的定义

English:
definition Fan.isLimitMapConeEquiv
  signature: (F : C ⥤ D) {ι : Type*} (X : ι -> C) (c : Fan X)
  body: (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans
    IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

中文:
定义 Fan.isLimitMapConeEquiv
  签名: (F : C ⥤ D) {ι : 类型} (X : ι -> C) (c : Fan X)
  定义体: (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans
    IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

Depends on / 依赖: Cone.ext, Discrete, Discrete.natIsoFunctor, F.mapCone, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, equivIsoLimit, mapCone, natIsoFunctor, postcomposeHomEquiv, symm.trans
-/
def Fan.isLimitMapConeEquiv (F : C ⥤ D) {ι : Type*} (X : ι -> C) (c : Fan X) :
    IsLimit (F.mapCone c) ≃ IsLimit (Fan.mk _ fun i => F.map (c.proj i)) :=
(IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans
    IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

/--
Definition of `Cofan.isColimitMapCoconeEquiv` / `Cofan.isColimitMapCoconeEquiv` 的定义

English:
definition Cofan.isColimitMapCoconeEquiv
  signature: (F : C ⥤ D) {ι : Type*} (X : ι -> C) (c : Cofan X)
  body: (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm (F.mapCocone c)).symm.trans
    IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

中文:
定义 Cofan.isColimitMapCoconeEquiv
  签名: (F : C ⥤ D) {ι : 类型} (X : ι -> C) (c : Cofan X)
  定义体: (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm (F.mapCocone c)).symm.trans
    IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

Depends on / 依赖: Cocone, Cocone.ext, Discrete, Discrete.natIsoFunctor.symm, F.mapCocone, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, equivIsoColimit, mapCocone, natIsoFunctor, precomposeHomEquiv, symm.trans
-/
def Cofan.isColimitMapCoconeEquiv (F : C ⥤ D) {ι : Type*} (X : ι -> C) (c : Cofan X) :
    IsColimit (F.mapCocone c) ≃ IsColimit (Cofan.mk _ fun i => F.map (c.inj i)) :=
(IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm (F.mapCocone c)).symm.trans
    IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

end Comparison

variable (C)

/--
Definition of `HasProducts` / `HasProducts` 的定义

English:
abbreviation HasProducts
  body: forall J : Type w, HasLimitsOfShape (Discrete J) C

中文:
缩写 HasProducts
  定义体: forall J : Type w, HasLimitsOfShape (Discrete J) C

Depends on / 依赖: Discrete, HasLimitsOfShape
-/
abbrev HasProducts :=
  forall J : Type w, HasLimitsOfShape (Discrete J) C

/--
Definition of `HasCoproducts` / `HasCoproducts` 的定义

English:
abbreviation HasCoproducts
  body: forall J : Type w, HasColimitsOfShape (Discrete J) C

中文:
缩写 HasCoproducts
  定义体: forall J : Type w, HasColimitsOfShape (Discrete J) C

Depends on / 依赖: Discrete, HasColimitsOfShape
-/
abbrev HasCoproducts :=
  forall J : Type w, HasColimitsOfShape (Discrete J) C

variable {C}

/--
lemma `hasProducts_shrink` / 引理 `hasProducts_shrink`

English:
lemma hasProducts_shrink
  given: [HasProducts.{max w w'} C]
  statement: HasProducts.{w} C
  proof: fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

中文:
引理 hasProducts_shrink
  条件: [HasProducts.{最大值 w w'} C]
  结论: HasProducts.{w} C
  证明: fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)
-/
lemma hasProducts_shrink [HasProducts.{max w w'} C] : HasProducts.{w} C := fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

/--
lemma `hasCoproducts_shrink` / 引理 `hasCoproducts_shrink`

English:
lemma hasCoproducts_shrink
  given: [HasCoproducts.{max w w'} C]
  statement: HasCoproducts.{w} C
  proof: fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

中文:
引理 hasCoproducts_shrink
  条件: [HasCoproducts.{最大值 w w'} C]
  结论: HasCoproducts.{w} C
  证明: fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)
-/
lemma hasCoproducts_shrink [HasCoproducts.{max w w'} C] : HasCoproducts.{w} C := fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)

/--
theorem `has_smallest_products_of_hasProducts` / 定理 `has_smallest_products_of_hasProducts`

English:
theorem has_smallest_products_of_hasProducts
  given: [HasProducts.{w} C]
  statement: HasProducts.{0} C
  proof: hasProducts_shrink

中文:
定理 has_smallest_products_of_hasProducts
  条件: [HasProducts.{w} C]
  结论: HasProducts.{0} C
  证明: hasProducts_shrink

Depends on / 依赖: hasProducts_shrink
-/
theorem has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0} C :=
  hasProducts_shrink

/--
theorem `has_smallest_coproducts_of_hasCoproducts` / 定理 `has_smallest_coproducts_of_hasCoproducts`

English:
theorem has_smallest_coproducts_of_hasCoproducts
  given: [HasCoproducts.{w} C]
  statement: HasCoproducts.{0} C
  proof: hasCoproducts_shrink

中文:
定理 has_smallest_coproducts_of_hasCoproducts
  条件: [HasCoproducts.{w} C]
  结论: HasCoproducts.{0} C
  证明: hasCoproducts_shrink

Depends on / 依赖: hasCoproducts_shrink
-/
theorem has_smallest_coproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{0} C :=
  hasCoproducts_shrink

/--
theorem `hasProducts_of_limit_fans` / 定理 `hasProducts_of_limit_fans`

English:
theorem hasProducts_of_limit_fans
  statement: (lf : forall {J : Type w} (f : J -> C), Fan f)
  proof: fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }

中文:
定理 hasProducts_of_limit_fans
  结论: (lf : 对任意 {J : 类型 w} (f : J -> C), Fan f)
  证明: fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }

Depends on / 依赖: Cone.postcompose, Discrete, Discrete.natIsoFunctor.inv, F.obj, HasLimit, HasLimit.mk, IsLimit, IsLimit.postcomposeInvEquiv, has_limit, lf_isLimit, natIsoFunctor, postcompose, postcomposeInvEquiv
-/
theorem hasProducts_of_limit_fans (lf : forall {J : Type w} (f : J -> C), Fan f)
    (lf_isLimit : forall {J : Type w} (f : J -> C), IsLimit (lf f)) : HasProducts.{w} C :=
  fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }

/--
theorem `hasCoproducts_of_colimit_cofans` / 定理 `hasCoproducts_of_colimit_cofans`

English:
theorem hasCoproducts_of_colimit_cofans
  statement: (cf : forall {J : Type w} (f : J -> C), Cofan f)
  proof: fun _ : Type w =>
  { has_colimit := fun F =>
      HasColimit.mk
        ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj (cf fun j => F.obj ⟨j⟩),
          (IsColimit.precomposeHomEquiv _ _).symm (cf_isColimit _)⟩ }

中文:
定理 hasCoproducts_of_colimit_cofans
  结论: (cf : 对任意 {J : 类型 w} (f : J -> C), Cofan f)
  证明: fun _ : Type w =>
  { has_colimit := fun F =>
      HasColimit.mk
        ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj (cf fun j => F.obj ⟨j⟩),
          (IsColimit.precomposeHomEquiv _ _).symm (cf_isColimit _)⟩ }

Depends on / 依赖: Cocone, Cocone.precompose, Discrete, Discrete.natIsoFunctor.hom, F.obj, HasColimit, HasColimit.mk, IsColimit, IsColimit.precomposeHomEquiv, cf_isColimit, has_colimit, natIsoFunctor, precompose, precomposeHomEquiv
-/
theorem hasCoproducts_of_colimit_cofans (cf : forall {J : Type w} (f : J -> C), Cofan f)
    (cf_isColimit : forall {J : Type w} (f : J -> C), IsColimit (cf f)) : HasCoproducts.{w} C :=
  fun _ : Type w =>
  { has_colimit := fun F =>
      HasColimit.mk
        ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj (cf fun j => F.obj ⟨j⟩),
          (IsColimit.precomposeHomEquiv _ _).symm (cf_isColimit _)⟩ }

instance (priority := 100) hasProductsOfShape_of_hasProducts [HasProducts.{w} C] (J : Type w) :
    HasProductsOfShape J C := inferInstance

instance (priority := 100) hasCoproductsOfShape_of_hasCoproducts [HasCoproducts.{w} C]
    (J : Type w) : HasCoproductsOfShape J C := inferInstance

open Opposite in
/-- The functor sending `(X, n)` to the product of copies of `X` indexed by `n`. -/
@[implicit_reducible, simps]
/--
Definition of `piConst` / `piConst` 的定义

English:
definition piConst
  signature: [Limits.HasProducts.{w} C]
  body: { obj n := ∏ᶜ fun _ : (unop n :) => X, map f := Limits.Pi.map' f.unop fun _ => 𝟙 _ }
  map f := { app n := Limits.Pi.map fun _ => f }

中文:
定义 piConst
  签名: [Limits.HasProducts.{w} C]
  定义体: { obj n := ∏ᶜ fun _ : (unop n :) => X, map f := Limits.Pi.map' f.unop fun _ => 𝟙 _ }
  map f := { app n := Limits.Pi.map fun _ => f }

Depends on / 依赖: Limits, Limits.Pi.map, f.unop
-/
def piConst [Limits.HasProducts.{w} C] : C ⥤ Type wᵒᵖ ⥤ C where
  obj X := { obj n := ∏ᶜ fun _ : (unop n :) => X, map f := Limits.Pi.map' f.unop fun _ => 𝟙 _ }
  map f := { app n := Limits.Pi.map fun _ => f }

/--
Definition of `piConstAdj` / `piConstAdj` 的定义

English:
definition piConstAdj
  signature: [Limits.HasProducts.{v} C] (X : C)
  body: { app n := ↾fun i => Limits.Pi.π (fun _ : n => X) i }
  counit :=
  { app Y := (Limits.Pi.lift id).op,
    naturality _ _ _ := by apply Quiver.Hom.unop_inj; cat_disch }
  left_triangle_components _ := by apply Quiver.Hom.unop_inj; cat_disch

中文:
定义 piConstAdj
  签名: [Limits.HasProducts.{v} C] (X : C)
  定义体: { app n := ↾fun i => Limits.Pi.π (fun _ : n => X) i }
  counit :=
  { app Y := (Limits.Pi.lift id).op,
    naturality _ _ _ := by apply Quiver.Hom.unop_inj; cat_disch }
  left_triangle_components _ := by apply Quiver.Hom.unop_inj; cat_disch

Depends on / 依赖: Limits, Limits.Pi
-/
def piConstAdj [Limits.HasProducts.{v} C] (X : C) :
    (piConst.obj X).rightOp ⊣ yoneda.obj X where
  unit := { app n := ↾fun i => Limits.Pi.π (fun _ : n => X) i }
  counit :=
  { app Y := (Limits.Pi.lift id).op,
    naturality _ _ _ := by apply Quiver.Hom.unop_inj; cat_disch }
  left_triangle_components _ := by apply Quiver.Hom.unop_inj; cat_disch

/-- The functor sending `(X, n)` to the coproduct of copies of `X` indexed by `n`. -/
@[implicit_reducible, simps]
/--
Definition of `sigmaConst` / `sigmaConst` 的定义

English:
definition sigmaConst
  signature: [Limits.HasCoproducts.{w} C]
  body: { obj n := ∐ fun _ : n => X, map f := Limits.Sigma.map' f fun _ => 𝟙 _ }
  map f := { app n := Limits.Sigma.map fun _ => f }

中文:
定义 sigmaConst
  签名: [Limits.HasCoproducts.{w} C]
  定义体: { obj n := ∐ fun _ : n => X, map f := Limits.Sigma.map' f fun _ => 𝟙 _ }
  map f := { app n := Limits.Sigma.map fun _ => f }

Depends on / 依赖: Limits, Limits.Sigma.map
-/
def sigmaConst [Limits.HasCoproducts.{w} C] : C ⥤ Type w ⥤ C where
  obj X := { obj n := ∐ fun _ : n => X, map f := Limits.Sigma.map' f fun _ => 𝟙 _ }
  map f := { app n := Limits.Sigma.map fun _ => f }

/--
Definition of `sigmaConstAdj` / `sigmaConstAdj` 的定义

English:
definition sigmaConstAdj
  signature: [Limits.HasCoproducts.{v} C] (X : C)
  body: { app n := ↾fun i => Limits.Sigma.ι (fun _ : n => X) i }
  counit := { app Y := Limits.Sigma.desc id }

中文:
定义 sigmaConstAdj
  签名: [Limits.HasCoproducts.{v} C] (X : C)
  定义体: { app n := ↾fun i => Limits.Sigma.ι (fun _ : n => X) i }
  counit := { app Y := Limits.Sigma.desc id }

Depends on / 依赖: Limits, Limits.Sigma
-/
def sigmaConstAdj [Limits.HasCoproducts.{v} C] (X : C) :
    sigmaConst.obj X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app n := ↾fun i => Limits.Sigma.ι (fun _ : n => X) i }
  counit := { app Y := Limits.Sigma.desc id }

/-!
(Co)products over a type with a unique term.
-/


section Unique

/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
/--
Definition of `limitConeOfUnique` / `limitConeOfUnique` 的定义

English:
definition limitConeOfUnique
  signature: [Unique β] (f : β -> C)
  body: { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }

中文:
定义 limitConeOfUnique
  签名: [唯一 β] (f : β -> C)
  定义体: { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }

Depends on / 依赖: Discrete, Discrete.natTrans, Subsingleton, Subsingleton.elim, eqToHom, isLimit, natTrans, specialize, subsingleton
-/
def limitConeOfUnique [Unique β] (f : β -> C) : LimitCone (Discrete.functor f) where
  cone :=
    { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }

instance (priority := 100) hasProduct_unique [Nonempty β] [Subsingleton β] (f : β -> C) :
    HasProduct f :=
  let ⟨_⟩ := nonempty_unique β; HasLimit.mk (limitConeOfUnique f)

/--
Definition of `productUniqueIso` / `productUniqueIso` 的定义

English:
definition productUniqueIso
  signature: [Unique β] (f : β -> C)
  body: IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

@[simp]

中文:
定义 productUniqueIso
  签名: [唯一 β] (f : β -> C)
  定义体: IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit, limitConeOfUnique
-/
def productUniqueIso [Unique β] (f : β -> C) : ∏ᶜ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

@[simp]
/--
lemma `productUniqueIso_hom` / 引理 `productUniqueIso_hom`

English:
lemma productUniqueIso_hom
  given: [Unique β] (f : β -> C)
  statement: (productUniqueIso f).hom = Pi.π f default
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 productUniqueIso_hom
  条件: [唯一 β] (f : β -> C)
  结论: (productUniqueIso f).hom = 依赖函数类型.π f default
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma productUniqueIso_hom [Unique β] (f : β -> C) : (productUniqueIso f).hom = Pi.π f default :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `productUniqueIso_inv_π` / 引理 `productUniqueIso_inv_π`

English:
lemma productUniqueIso_inv_π
  given: [Unique β] (f : β -> C) (b : β)
  proof: by
  obtain rfl := Subsingleton.allEq b default
  simp [Iso.inv_comp_eq]

@[deprecated (since := "2026-06-30")] alias productUniqueIso_inv := productUniqueIso_inv_π

中文:
引理 productUniqueIso_inv_π
  条件: [唯一 β] (f : β -> C) (b : β)
  证明: by
  obtain rfl := Subsingleton.allEq b default
  simp [Iso.inv_comp_eq]

@[deprecated (since := "2026-06-30")] alias productUniqueIso_inv := productUniqueIso_inv_π

Depends on / 依赖: Iso.inv_comp_eq, Subsingleton, Subsingleton.allEq, inv_comp_eq
-/
lemma productUniqueIso_inv_π [Unique β] (f : β -> C) (b : β) :
    (productUniqueIso f).inv ≫ Pi.π f b = eqToHom (congrArg _ <| Subsingleton.allEq _ _) := by
  obtain rfl := Subsingleton.allEq b default
  simp [Iso.inv_comp_eq]

@[deprecated (since := "2026-06-30")] alias productUniqueIso_inv := productUniqueIso_inv_π

/--
Definition of `Fan.isLimitMkOfUnique` / `Fan.isLimitMkOfUnique` 的定义

English:
definition Fan.isLimitMkOfUnique
  signature: {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J]
  body: by
  refine Fan.IsLimit.mk _ (fun s => s.proj default ≫ e.inv) (fun s j => ?_) fun s m hm => ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_mono e.hom] using hm default

中文:
定义 Fan.isLimitMkOfUnique
  签名: {X Y : C} (e : X ≅ Y) (J : 类型) [唯一 J]
  定义体: by
  refine Fan.IsLimit.mk _ (fun s => s.proj default ≫ e.inv) (fun s j => ?_) fun s m hm => ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_mono e.hom] using hm default

Depends on / 依赖: Fan.IsLimit.mk, IsLimit, Subsingleton, Subsingleton.elim, cancel_mono, e.hom, e.inv, s.proj
-/
def Fan.isLimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsLimit (Fan.mk X fun _ : J => e.hom) := by
  refine Fan.IsLimit.mk _ (fun s => s.proj default ≫ e.inv) (fun s j => ?_) fun s m hm => ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_mono e.hom] using hm default

/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
/--
Definition of `colimitCoconeOfUnique` / `colimitCoconeOfUnique` 的定义

English:
definition colimitCoconeOfUnique
  signature: [Unique β] (f : β -> C)
  body: { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isColimit :=
    { desc := fun s => s.ι.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        apply Category.id_comp
      uniq := fun s m w => by
        specialize w default
        simp_all }

中文:
定义 colimitCoconeOfUnique
  签名: [唯一 β] (f : β -> C)
  定义体: { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isColimit :=
    { desc := fun s => s.ι.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        apply Category.id_comp
      uniq := fun s m w => by
        specialize w default
        simp_all }

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.natTrans, Subsingleton, Subsingleton.elim, eqToHom, id_comp, isColimit, natTrans, specialize, subsingleton
-/
def colimitCoconeOfUnique [Unique β] (f : β -> C) : ColimitCocone (Discrete.functor f) where
  cocone :=
    { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isColimit :=
    { desc := fun s => s.ι.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        apply Category.id_comp
      uniq := fun s m w => by
        specialize w default
        simp_all }

instance (priority := 100) hasCoproduct_unique [Nonempty β] [Subsingleton β] (f : β -> C) :
    HasCoproduct f :=
  let ⟨_⟩ := nonempty_unique β; HasColimit.mk (colimitCoconeOfUnique f)

/--
Definition of `coproductUniqueIso` / `coproductUniqueIso` 的定义

English:
definition coproductUniqueIso
  signature: [Unique β] (f : β -> C)
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit

@[simp]

中文:
定义 coproductUniqueIso
  签名: [唯一 β] (f : β -> C)
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit

@[simp]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitCoconeOfUnique, isColimit
-/
def coproductUniqueIso [Unique β] (f : β -> C) : ∐ f ≅ f default :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit

@[simp]
/--
lemma `coproductUniqueIso_inv` / 引理 `coproductUniqueIso_inv`

English:
lemma coproductUniqueIso_inv
  given: [Unique β] (f : β -> C)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 coproductUniqueIso_inv
  条件: [唯一 β] (f : β -> C)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma coproductUniqueIso_inv [Unique β] (f : β -> C) :
    (coproductUniqueIso f).inv = Sigma.ι f default :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `ι_coproductUniqueIso_hom` / 引理 `ι_coproductUniqueIso_hom`

English:
lemma ι_coproductUniqueIso_hom
  given: [Unique β] (f : β -> C) (b : β)
  proof: by
  obtain rfl := Subsingleton.allEq b default
  symm
  simp [← Iso.comp_inv_eq]

@[deprecated (since := "2026-06-30")] alias coproductUniqueIso_hom := ι_coproductUniqueIso_hom

中文:
引理 ι_coproductUniqueIso_hom
  条件: [唯一 β] (f : β -> C) (b : β)
  证明: by
  obtain rfl := Subsingleton.allEq b default
  symm
  simp [← Iso.comp_inv_eq]

@[deprecated (since := "2026-06-30")] alias coproductUniqueIso_hom := ι_coproductUniqueIso_hom

Depends on / 依赖: Iso.comp_inv_eq, Subsingleton, Subsingleton.allEq, comp_inv_eq
-/
lemma ι_coproductUniqueIso_hom [Unique β] (f : β -> C) (b : β) :
    Sigma.ι f b ≫ (coproductUniqueIso f).hom = eqToHom (congrArg _ <| Subsingleton.allEq _ _) := by
  obtain rfl := Subsingleton.allEq b default
  symm
  simp [← Iso.comp_inv_eq]

@[deprecated (since := "2026-06-30")] alias coproductUniqueIso_hom := ι_coproductUniqueIso_hom

/--
Definition of `Cofan.isColimitMkOfUnique` / `Cofan.isColimitMkOfUnique` 的定义

English:
definition Cofan.isColimitMkOfUnique
  signature: {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J]
  body: by
  refine Cofan.IsColimit.mk _ (fun s => e.inv ≫ s.inj default) (fun s j => ?_) fun s m hm => ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_epi e.hom] using hm default

中文:
定义 Cofan.isColimitMkOfUnique
  签名: {X Y : C} (e : X ≅ Y) (J : 类型) [唯一 J]
  定义体: by
  refine Cofan.IsColimit.mk _ (fun s => e.inv ≫ s.inj default) (fun s j => ?_) fun s m hm => ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_epi e.hom] using hm default

Depends on / 依赖: Cofan.IsColimit.mk, IsColimit, Subsingleton, Subsingleton.elim, cancel_epi, e.hom, e.inv, s.inj
-/
def Cofan.isColimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsColimit (Cofan.mk Y fun _ : J => e.hom) := by
  refine Cofan.IsColimit.mk _ (fun s => e.inv ≫ s.inj default) (fun s j => ?_) fun s m hm => ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_epi e.hom] using hm default

end Unique

section Reindex

variable {γ : Type w'} (ε : β ≃ γ) (f : γ -> C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/--
Definition of `Pi.reindex` / `Pi.reindex` 的定义

English:
definition Pi.reindex
  signature: : piObj (f ∘ ε) ≅ piObj f
  body: HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

中文:
定义 依赖函数类型.reindex
  签名: : piObj (f ∘ ε) ≅ piObj f
  定义体: HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

Depends on / 依赖: Discrete, Discrete.equivalence, Discrete.natIso, HasLimit, HasLimit.isoOfEquivalence, Iso.refl, equivalence, isoOfEquivalence, natIso
-/
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `Pi.reindex_hom_π` / 定理 `Pi.reindex_hom_π`

English:
theorem Pi.reindex_hom_π
  given: (b : β)
  statement: (Pi.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b
  proof: by
  dsimp [Pi.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]

中文:
定理 依赖函数类型.reindex_hom_π
  条件: (b : β)
  结论: (依赖函数类型.reindex ε f).hom ≫ 依赖函数类型.π f (ε b) = 依赖函数类型.π (f ∘ ε) b
  证明: by
  dsimp [Pi.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.eqToHom, Discrete.equivalence_functor, Discrete.equivalence_inverse, Discrete.functor, Discrete.functor_obj, Discrete.natIso_inv_app, Function, Function.comp_apply, Functor, Functor.comp_obj, Functor.id_obj, HasLimit, HasLimit.isoOfEquivalence_hom_, Iso.refl_inv, Pi.reindex, comp_apply, comp_obj
-/
theorem Pi.reindex_hom_π (b : β) : (Pi.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp [Pi.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]
/--
theorem `Pi.reindex_inv_π` / 定理 `Pi.reindex_inv_π`

English:
theorem Pi.reindex_inv_π
  given: (b : β)
  statement: (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b)
  proof: by
  simp [Iso.inv_comp_eq]

中文:
定理 依赖函数类型.reindex_inv_π
  条件: (b : β)
  结论: (依赖函数类型.reindex ε f).inv ≫ 依赖函数类型.π (f ∘ ε) b = 依赖函数类型.π f (ε b)
  证明: by
  simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem Pi.reindex_inv_π (b : β) : (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [Iso.inv_comp_eq]

variable {f} in
/--
Definition of `Fan.isLimitEquivOfEquiv` / `Fan.isLimitEquivOfEquiv` 的定义

English:
definition Fan.isLimitEquivOfEquiv
  signature: (c : Fan f)
  body: IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

中文:
定义 Fan.isLimitEquivOfEquiv
  签名: (c : Fan f)
  定义体: IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

Depends on / 依赖: Discrete, Discrete.equivalence, IsLimit, IsLimit.whiskerEquivalenceEquiv, equivalence, whiskerEquivalenceEquiv
-/
def Fan.isLimitEquivOfEquiv (c : Fan f) :
    IsLimit c ≃ IsLimit (Fan.mk _ fun i : β => c.proj (ε i)) :=
  IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end

section

variable [HasCoproduct f] [HasCoproduct (f ∘ ε)]

/--
Definition of `Sigma.reindex` / `Sigma.reindex` 的定义

English:
definition Sigma.reindex
  signature: : sigmaObj (f ∘ ε) ≅ sigmaObj f
  body: HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

中文:
定义 依赖和类型.reindex
  签名: : sigmaObj (f ∘ ε) ≅ sigmaObj f
  定义体: HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

Depends on / 依赖: Discrete, Discrete.equivalence, Discrete.natIso, HasColimit, HasColimit.isoOfEquivalence, Iso.refl, equivalence, isoOfEquivalence, natIso
-/
def Sigma.reindex : sigmaObj (f ∘ ε) ≅ sigmaObj f :=
  HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `Sigma.ι_reindex_hom` / 定理 `Sigma.ι_reindex_hom`

English:
theorem Sigma.ι_reindex_hom
  given: (b : β)
  proof: by
  dsimp [Sigma.reindex]
  simp only [HasColimit.ι_isoOfEquivalence_hom, Functor.id_obj, Discrete.functor_obj,
    Function.comp_apply, Discrete.equivalence_functor, Discrete.equivalence_inverse,
    Functor.comp_obj, Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  have h := colimit.w (Discrete.functor f) (Discrete.eqToHom' (ε.apply_symm_apply (ε b)))
  simp only [Discrete.functor_obj] at h
  erw [← h, eqToHom_map, eqToHom_map, eqToHom_trans_assoc]
  all_goals { simp }

@[reassoc (attr := simp)]

中文:
定理 依赖和类型.ι_reindex_hom
  条件: (b : β)
  证明: by
  dsimp [Sigma.reindex]
  simp only [HasColimit.ι_isoOfEquivalence_hom, Functor.id_obj, Discrete.functor_obj,
    Function.comp_apply, Discrete.equivalence_functor, Discrete.equivalence_inverse,
    Functor.comp_obj, Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  have h := colimit.w (Discrete.functor f) (Discrete.eqToHom' (ε.apply_symm_apply (ε b)))
  simp only [Discrete.functor_obj] at h
  erw [← h, eqToHom_map, eqToHom_map, eqToHom_trans_assoc]
  all_goals { simp }

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.eqToHom, Discrete.equivalence_functor, Discrete.equivalence_inverse, Discrete.functor, Discrete.functor_obj, Discrete.natIso_inv_app, Function, Function.comp_apply, Functor, Functor.comp_obj, Functor.id_obj, HasColimit, Iso.refl_inv, Sigma.reindex, all_goals, apply_symm_apply, colimit
-/
theorem Sigma.ι_reindex_hom (b : β) :
    Sigma.ι (f ∘ ε) b ≫ (Sigma.reindex ε f).hom = Sigma.ι f (ε b) := by
  dsimp [Sigma.reindex]
  simp only [HasColimit.ι_isoOfEquivalence_hom, Functor.id_obj, Discrete.functor_obj,
    Function.comp_apply, Discrete.equivalence_functor, Discrete.equivalence_inverse,
    Functor.comp_obj, Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  have h := colimit.w (Discrete.functor f) (Discrete.eqToHom' (ε.apply_symm_apply (ε b)))
  simp only [Discrete.functor_obj] at h
  erw [← h, eqToHom_map, eqToHom_map, eqToHom_trans_assoc]
  all_goals { simp }

@[reassoc (attr := simp)]
/--
theorem `Sigma.ι_reindex_inv` / 定理 `Sigma.ι_reindex_inv`

English:
theorem Sigma.ι_reindex_inv
  given: (b : β)
  proof: by simp [Iso.comp_inv_eq]

中文:
定理 依赖和类型.ι_reindex_inv
  条件: (b : β)
  证明: by simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem Sigma.ι_reindex_inv (b : β) :
    Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b := by simp [Iso.comp_inv_eq]

variable {f} in
/--
Definition of `Cofan.isColimitEquivOfEquiv` / `Cofan.isColimitEquivOfEquiv` 的定义

English:
definition Cofan.isColimitEquivOfEquiv
  signature: (c : Cofan f)
  body: IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

中文:
定义 Cofan.isColimitEquivOfEquiv
  签名: (c : Cofan f)
  定义体: IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

Depends on / 依赖: Discrete, Discrete.equivalence, IsColimit, IsColimit.whiskerEquivalenceEquiv, equivalence, whiskerEquivalenceEquiv
-/
def Cofan.isColimitEquivOfEquiv (c : Cofan f) :
    IsColimit c ≃ IsColimit (Cofan.mk _ fun i : β => c.inj (ε i)) :=
  IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end

end Reindex

section

variable {J : Type u₂} [Category.{v₂} J] (F : J ⥤ C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimit
  signature: F] [HasProduct F.obj] : Mono (Pi.lift (limit.π F)) where
  body: by
    refine limit.hom_ext fun j => ?_
    simpa using h =≫ Pi.π _ j

中文:
实例 [有极限
  签名: F] [HasProduct F.obj] : 单态射 (依赖函数类型.lift (limit.π F)) where
  定义体: by
    refine limit.hom_ext fun j => ?_
    simpa using h =≫ Pi.π _ j

Depends on / 依赖: hom_ext, limit.hom_ext
-/
instance [HasLimit F] [HasProduct F.obj] : Mono (Pi.lift (limit.π F)) where
  right_cancellation _ _ h := by
    refine limit.hom_ext fun j => ?_
    simpa using h =≫ Pi.π _ j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimit
  signature: F] [HasCoproduct F.obj] : Epi (Sigma.desc (colimit.ι F)) where
  body: by
    refine colimit.hom_ext fun j => ?_
    simpa using Sigma.ι _ j ≫= h

中文:
实例 [有余极限
  签名: F] [HasCoproduct F.obj] : 满态射 (依赖和类型.desc (colimit.ι F)) where
  定义体: by
    refine colimit.hom_ext fun j => ?_
    simpa using Sigma.ι _ j ≫= h

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext
-/
instance [HasColimit F] [HasCoproduct F.obj] : Epi (Sigma.desc (colimit.ι F)) where
  left_cancellation _ _ h := by
    refine colimit.hom_ext fun j => ?_
    simpa using Sigma.ι _ j ≫= h

end

section Thin

variable [Quiver.IsThin C] {J : Type*} [Category* J] {K : J ⥤ C}

/--
Definition of `isLimitEquivFanOfIsThin` / `isLimitEquivFanOfIsThin` 的定义

English:
definition isLimitEquivFanOfIsThin
  signature: (c : Cone K)
  body: Fan.IsLimit.mk _ (fun s => hc.lift { pt := s.pt, π.app j := s.proj j })
    (by subsingleton) (by subsingleton)
  invFun h := { lift s := Fan.IsLimit.lift h s.π.app }

中文:
定义 isLimitEquivFanOfIsThin
  签名: (c : 锥 K)
  定义体: Fan.IsLimit.mk _ (fun s => hc.lift { pt := s.pt, π.app j := s.proj j })
    (by subsingleton) (by subsingleton)
  invFun h := { lift s := Fan.IsLimit.lift h s.π.app }

Depends on / 依赖: Fan.IsLimit.mk, IsLimit, hc.lift, s.proj, s.pt
-/
def isLimitEquivFanOfIsThin (c : Cone K) : IsLimit c ≃ IsLimit (Fan.mk c.pt c.π.app) where
  toFun hc := Fan.IsLimit.mk _ (fun s => hc.lift { pt := s.pt, π.app j := s.proj j })
    (by subsingleton) (by subsingleton)
  invFun h := { lift s := Fan.IsLimit.lift h s.π.app }

/--
Definition of `isColimitEquivCofanOfIsThin` / `isColimitEquivCofanOfIsThin` 的定义

English:
definition isColimitEquivCofanOfIsThin
  signature: (c : Cocone K)
  body: Cofan.IsColimit.mk _ (fun s => hc.desc { pt := s.pt, ι.app j := s.inj j })
    (by subsingleton) (by subsingleton)
  invFun h := { desc s := Cofan.IsColimit.desc h s.ι.app }

中文:
定义 isColimitEquivCofanOfIsThin
  签名: (c : 余锥 K)
  定义体: Cofan.IsColimit.mk _ (fun s => hc.desc { pt := s.pt, ι.app j := s.inj j })
    (by subsingleton) (by subsingleton)
  invFun h := { desc s := Cofan.IsColimit.desc h s.ι.app }

Depends on / 依赖: Cofan.IsColimit.mk, IsColimit, hc.desc, s.inj, s.pt
-/
def isColimitEquivCofanOfIsThin (c : Cocone K) :
    IsColimit c ≃ IsColimit (Cofan.mk c.pt c.ι.app) where
  toFun hc := Cofan.IsColimit.mk _ (fun s => hc.desc { pt := s.pt, ι.app j := s.inj j })
    (by subsingleton) (by subsingleton)
  invFun h := { desc s := Cofan.IsColimit.desc h s.ι.app }

end Thin

section Fubini

variable {ι ι' : Type*} {X : ι -> ι' -> C}

/--
Definition of `Fan.IsLimit.prod` / `Fan.IsLimit.prod` 的定义

English:
definition Fan.IsLimit.prod
  signature: (c : forall i : ι, Fan (fun j : ι' => X i j)) (hc : forall i : ι, IsLimit (c i))
  body: by
  refine Fan.IsLimit.mk _ (fun t => ?_) ?_ fun t m hm => ?_
  · exact Fan.IsLimit.lift hc' fun i => Fan.IsLimit.lift (hc i) fun j => t.proj (i, j)
  · simp
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i => ?_
    exact Fan.IsLimit.hom_ext (hc i) _ _ fun j => (by simpa using hm (i, j))

中文:
定义 Fan.是极限.乘积
  签名: (c : 对任意 i : ι, Fan (fun j : ι' => X i j)) (hc : 对任意 i : ι, 是极限 (c i))
  定义体: by
  refine Fan.IsLimit.mk _ (fun t => ?_) ?_ fun t m hm => ?_
  · exact Fan.IsLimit.lift hc' fun i => Fan.IsLimit.lift (hc i) fun j => t.proj (i, j)
  · simp
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i => ?_
    exact Fan.IsLimit.hom_ext (hc i) _ _ fun j => (by simpa using hm (i, j))

Depends on / 依赖: Fan.IsLimit.hom_ext, Fan.IsLimit.lift, Fan.IsLimit.mk, IsLimit, hom_ext, t.proj
-/
def Fan.IsLimit.prod (c : forall i : ι, Fan (fun j : ι' => X i j)) (hc : forall i : ι, IsLimit (c i))
    (c' : Fan (fun i : ι => (c i).pt)) (hc' : IsLimit c') :
    (IsLimit <| Fan.mk c'.pt fun p : ι × ι' => c'.proj _ ≫ (c p.1).proj p.2) := by
  refine Fan.IsLimit.mk _ (fun t => ?_) ?_ fun t m hm => ?_
  · exact Fan.IsLimit.lift hc' fun i => Fan.IsLimit.lift (hc i) fun j => t.proj (i, j)
  · simp
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i => ?_
    exact Fan.IsLimit.hom_ext (hc i) _ _ fun j => (by simpa using hm (i, j))

/--
Definition of `Cofan.IsColimit.prod` / `Cofan.IsColimit.prod` 的定义

English:
definition Cofan.IsColimit.prod
  signature: (c : forall i : ι, Cofan (fun j : ι' => X i j)) (hc : forall i : ι, IsColimit (c i))
  body: by
  refine Cofan.IsColimit.mk _ (fun t => ?_) ?_ fun t m hm => ?_
  · exact Cofan.IsColimit.desc hc' fun i => Cofan.IsColimit.desc (hc i) fun j => t.inj (i, j)
  · simp
  · refine Cofan.IsColimit.hom_ext hc' _ _ fun i => ?_
    exact Cofan.IsColimit.hom_ext (hc i) _ _ fun j => (by simpa using hm (i, j))

中文:
定义 Cofan.是余极限.乘积
  签名: (c : 对任意 i : ι, Cofan (fun j : ι' => X i j)) (hc : 对任意 i : ι, 是余极限 (c i))
  定义体: by
  refine Cofan.IsColimit.mk _ (fun t => ?_) ?_ fun t m hm => ?_
  · exact Cofan.IsColimit.desc hc' fun i => Cofan.IsColimit.desc (hc i) fun j => t.inj (i, j)
  · simp
  · refine Cofan.IsColimit.hom_ext hc' _ _ fun i => ?_
    exact Cofan.IsColimit.hom_ext (hc i) _ _ fun j => (by simpa using hm (i, j))

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.IsColimit.hom_ext, Cofan.IsColimit.mk, IsColimit, hom_ext, t.inj
-/
def Cofan.IsColimit.prod (c : forall i : ι, Cofan (fun j : ι' => X i j)) (hc : forall i : ι, IsColimit (c i))
    (c' : Cofan (fun i : ι => (c i).pt)) (hc' : IsColimit c') :
    (IsColimit <| Cofan.mk c'.pt fun p : ι × ι' => (c p.1).inj p.2 ≫ c'.inj _) := by
  refine Cofan.IsColimit.mk _ (fun t => ?_) ?_ fun t m hm => ?_
  · exact Cofan.IsColimit.desc hc' fun i => Cofan.IsColimit.desc (hc i) fun j => t.inj (i, j)
  · simp
  · refine Cofan.IsColimit.hom_ext hc' _ _ fun i => ?_
    exact Cofan.IsColimit.hom_ext (hc i) _ _ fun j => (by simpa using hm (i, j))

end Fubini

variable (α) in
/-- The functor `(f : α → C) ↦ ∏ᶜ f`. -/
@[simps]
/--
Definition of `Pi.functor` / `Pi.functor` 的定义

English:
definition Pi.functor
  signature: [HasProductsOfShape α C]
  body: ∏ᶜ f
  map {f g} t := Pi.map t

中文:
定义 依赖函数类型.functor
  签名: [HasProductsOfShape α C]
  定义体: ∏ᶜ f
  map {f g} t := Pi.map t

Depends on / 依赖: RespectsIso, RespectsIso.postcomp, RespectsIso.precomp, postcomp, precomp
-/
noncomputable def Pi.functor [HasProductsOfShape α C] : (α -> C) ⥤ C where
  obj f := ∏ᶜ f
  map {f g} t := Pi.map t

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation induced by `Pi.π`. -/
@[simps]
/--
Definition of `Pi.functorπ` / `Pi.functorπ` 的定义

English:
definition Pi.functorπ
  signature: [HasProductsOfShape α C] (a : α)
  body: Pi.π f a

中文:
定义 依赖函数类型.functorπ
  签名: [HasProductsOfShape α C] (a : α)
  定义体: Pi.π f a
-/
def Pi.functorπ [HasProductsOfShape α C] (a : α) :
    Pi.functor α ⟶ Pi.eval (fun _ => C) a where
  app f := Pi.π f a

set_option backward.defeqAttrib.useBackward true in
variable (α) in
/-- Up to pre-composing with an equivalence of categories, `Pi.functor` is isomorphic to `lim`. -/
@[simps!]
/--
Definition of `piEquivalenceFunctorDiscreteCompLim` / `piEquivalenceFunctorDiscreteCompLim` 的定义

English:
definition piEquivalenceFunctorDiscreteCompLim
  signature: [HasProductsOfShape α C]
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 piEquivalenceFunctorDiscreteCompLim
  签名: [HasProductsOfShape α C]
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def piEquivalenceFunctorDiscreteCompLim [HasProductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ lim ≅ Pi.functor _ :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `piEquivalenceFunctorDiscreteCompLim_comp_functorπ` / 引理 `piEquivalenceFunctorDiscreteCompLim_comp_functorπ`

English:
lemma piEquivalenceFunctorDiscreteCompLim_comp_functorπ
  given: [HasProductsOfShape α C] (a : α)
  proof: by
  cat_disch

中文:
引理 piEquivalenceFunctorDiscreteCompLim_comp_functorπ
  条件: [HasProductsOfShape α C] (a : α)
  证明: by
  cat_disch

Depends on / 依赖: Pi.functor
-/
lemma piEquivalenceFunctorDiscreteCompLim_comp_functorπ [HasProductsOfShape α C] (a : α) :
    (piEquivalenceFunctorDiscreteCompLim (C := C) α).hom ≫ Pi.functorπ a =
      Functor.whiskerLeft _ (lim.π <| Discrete.mk a) ≫
        (piEquivalenceFunctorDiscreteCompEvaluationIso _ _).hom := by
  cat_disch

attribute [local simp] Functor.pi in
/-- The `∏ᶜ` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)` is isomorphic
to the constant functor with value `∏ᶜ X`. -/
@[simps!]
/--
Definition of `Pi.constCompPiIsoConst` / `Pi.constCompPiIsoConst` 的定义

English:
definition Pi.constCompPiIsoConst
  signature: [HasProductsOfShape α C] {I : α -> Type*}
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 依赖函数类型.constCompPiIsoConst
  签名: [HasProductsOfShape α C] {I : α -> 类型}
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def Pi.constCompPiIsoConst [HasProductsOfShape α C] {I : α -> Type*}
    [forall i, Category* (I i)] (X : α -> C) :
    Functor.pi (fun i => (Functor.const (I i)).obj (X i)) ⋙ Pi.functor α ≅
      (Functor.const _).obj (∏ᶜ X) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

variable (α) in
/-- The functor `(f : α → C) ↦ ∐ f`. -/
@[simps]
/--
Definition of `Sigma.functor` / `Sigma.functor` 的定义

English:
definition Sigma.functor
  signature: [HasCoproductsOfShape α C]
  body: ∐ f
  map {f g} t := Sigma.map t

中文:
定义 依赖和类型.functor
  签名: [HasCoproductsOfShape α C]
  定义体: ∐ f
  map {f g} t := Sigma.map t
-/
noncomputable def Sigma.functor [HasCoproductsOfShape α C] : (α -> C) ⥤ C where
  obj f := ∐ f
  map {f g} t := Sigma.map t

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation induced by `Sigma.ι`. -/
@[simps]
/--
Definition of `Sigma.functorι` / `Sigma.functorι` 的定义

English:
definition Sigma.functorι
  signature: [HasCoproductsOfShape α C] (a : α)
  body: Sigma.ι f a

中文:
定义 依赖和类型.functorι
  签名: [HasCoproductsOfShape α C] (a : α)
  定义体: Sigma.ι f a
-/
def Sigma.functorι [HasCoproductsOfShape α C] (a : α) :
    Pi.eval (fun _ => C) a ⟶ Sigma.functor α where
  app f := Sigma.ι f a

set_option backward.defeqAttrib.useBackward true in
variable (α) in
/-- Up to pre-composing with an equivalence of categories, `Sigma.functor` is isomorphic
to `colim`. -/
@[simps!]
/--
Definition of `piEquivalenceFunctorDiscreteCompColim` / `piEquivalenceFunctorDiscreteCompColim` 的定义

English:
definition piEquivalenceFunctorDiscreteCompColim
  signature: [HasCoproductsOfShape α C]
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 piEquivalenceFunctorDiscreteCompColim
  签名: [HasCoproductsOfShape α C]
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def piEquivalenceFunctorDiscreteCompColim [HasCoproductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ colim ≅ Sigma.functor _ :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `piEquivalenceFunctorDiscreteCompColim_comp_functorι` / 引理 `piEquivalenceFunctorDiscreteCompColim_comp_functorι`

English:
lemma piEquivalenceFunctorDiscreteCompColim_comp_functorι
  given: [HasCoproductsOfShape α C] (a : α)
  proof: by
  cat_disch

中文:
引理 piEquivalenceFunctorDiscreteCompColim_comp_functorι
  条件: [HasCoproductsOfShape α C] (a : α)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma piEquivalenceFunctorDiscreteCompColim_comp_functorι [HasCoproductsOfShape α C] (a : α) :
    Functor.whiskerLeft _ (colim.ι <| .mk a) ≫ (piEquivalenceFunctorDiscreteCompColim α).hom =
      (piEquivalenceFunctorDiscreteCompEvaluationIso C _).hom ≫ Sigma.functorι a := by
  cat_disch

/--
lemma `piEquivalenceFunctorDiscrete_functor_comp_colim` / 引理 `piEquivalenceFunctorDiscrete_functor_comp_colim`

English:
lemma piEquivalenceFunctorDiscrete_functor_comp_colim
  given: [HasCoproductsOfShape α C]
  proof: rfl

中文:
引理 piEquivalenceFunctorDiscrete_functor_comp_colim
  条件: [HasCoproductsOfShape α C]
  证明: rfl
-/
lemma piEquivalenceFunctorDiscrete_functor_comp_colim [HasCoproductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ colim = Sigma.functor _ :=
  rfl

attribute [local simp] Functor.pi in
/-- The `∐` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)` is isomorphic
to the constant functor with value `∐ X`. -/
@[simps!]
/--
Definition of `Sigma.constCompSigmaIsoConst` / `Sigma.constCompSigmaIsoConst` 的定义

English:
definition Sigma.constCompSigmaIsoConst
  signature: [HasCoproductsOfShape α C] {I : α -> Type*}
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 依赖和类型.constCompSigmaIsoConst
  签名: [HasCoproductsOfShape α C] {I : α -> 类型}
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def Sigma.constCompSigmaIsoConst [HasCoproductsOfShape α C] {I : α -> Type*}
    [forall i, Category* (I i)] (X : α -> C) :
    Functor.pi (fun i => (Functor.const (I i)).obj (X i)) ⋙ Sigma.functor α ≅
      (Functor.const _).obj (∐ X) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- The functor `C ⥤ (Type w)ᵒᵖ ⥤ C` which sends `X : C` and `α : Type w` to
the product of copies of `X` indexed by `α`. -/
@[simps]
/--
Definition of `piFunctor` / `piFunctor` 的定义

English:
definition piFunctor
  signature: [HasProducts.{w} C]
  body: { obj α := ∏ᶜ (fun (t : α.unop) => X)
      map f := Pi.map' f.unop (fun _ => 𝟙 _) }
  map f := { app T := Pi.map (fun _ => f) }

中文:
定义 piFunctor
  签名: [HasProducts.{w} C]
  定义体: { obj α := ∏ᶜ (fun (t : α.unop) => X)
      map f := Pi.map' f.unop (fun _ => 𝟙 _) }
  map f := { app T := Pi.map (fun _ => f) }

Depends on / 依赖: Pi.map, f.unop
-/
def piFunctor [HasProducts.{w} C] :
    C ⥤ Type wᵒᵖ ⥤ C where
  obj X :=
    { obj α := ∏ᶜ (fun (t : α.unop) => X)
      map f := Pi.map' f.unop (fun _ => 𝟙 _) }
  map f := { app T := Pi.map (fun _ => f) }

/-- The functor `C ⥤ Type w ⥤ C` which sends `X : C` and `α : Type w` to
the coproduct of copies of `X` indexed by `α`. -/
@[simps]
/--
Definition of `sigmaFunctor` / `sigmaFunctor` 的定义

English:
definition sigmaFunctor
  signature: [HasCoproducts.{w} C]
  body: { obj α := ∐ (fun (t : α) => X)
      map f := Sigma.map' f (fun _ => 𝟙 _) }
  map f := { app T := Sigma.map (fun _ => f) }

中文:
定义 sigmaFunctor
  签名: [HasCoproducts.{w} C]
  定义体: { obj α := ∐ (fun (t : α) => X)
      map f := Sigma.map' f (fun _ => 𝟙 _) }
  map f := { app T := Sigma.map (fun _ => f) }

Depends on / 依赖: Sigma.map
-/
def sigmaFunctor [HasCoproducts.{w} C] :
    C ⥤ Type w ⥤ C where
  obj X :=
    { obj α := ∐ (fun (t : α) => X)
      map f := Sigma.map' f (fun _ => 𝟙 _) }
  map f := { app T := Sigma.map (fun _ => f) }

end CategoryTheory.Limits
