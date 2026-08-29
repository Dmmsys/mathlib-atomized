/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Subobjects in the category of structured arrows

We compute the subobjects of an object `A` in the category `StructuredArrow S T` for `T : C ⥤ D`
and `S : D` as a subtype of the subobjects of `A.right`. We deduce that `StructuredArrow S T` is
well-powered if `C` is.

## Main declarations
* `StructuredArrow.subobjectEquiv`: the order-equivalence between `Subobject A` and a subtype of
  `Subobject A.right`.

## Implementation notes
Our computation requires that `C` has all limits and `T` preserves all limits. Furthermore, we
require that the morphisms of `C` and `D` are in the same universe. It is possible that both of
these requirements can be relaxed by refining the results about limits in comma categories.

We also provide the dual results. As usual, we use `Subobject (op A)` for the quotient objects of
`A`.

-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

/--
Definition of `projectSubobject` / `projectSubobject` 的定义

English:
definition projectSubobject
  signature: [HasFiniteLimits C] [PreservesFiniteLimits T] {A : StructuredArrow S T}
  body: by
  refine Subobject.lift (fun P f hf => Subobject.mk f.right) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) ?_
  exact congr_arg CommaMorphism.right hi

@[simp]

中文:
定义 projectSubobject
  签名: [有有限极限 C] [保持FiniteLimits T] {A : 结构化箭头 S T}
  定义体: by
  refine Subobject.lift (fun P f hf => Subobject.mk f.right) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) ?_
  exact congr_arg CommaMorphism.right hi

@[simp]

Depends on / 依赖: CommaMorphism, CommaMorphism.right, Subobject, Subobject.lift, Subobject.mk, Subobject.mk_eq_mk_of_comm, congr_arg, f.right, mapIso, mk_eq_mk_of_comm
-/
def projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T] {A : StructuredArrow S T} :
    Subobject A -> Subobject A.right := by
  refine Subobject.lift (fun P f hf => Subobject.mk f.right) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) ?_
  exact congr_arg CommaMorphism.right hi

@[simp]
/--
theorem `projectSubobject_mk` / 定理 `projectSubobject_mk`

English:
theorem projectSubobject_mk
  statement: [HasFiniteLimits C] [PreservesFiniteLimits T]
  proof: rfl

中文:
定理 projectSubobject_mk
  结论: [有有限极限 C] [保持FiniteLimits T]
  证明: rfl
-/
theorem projectSubobject_mk [HasFiniteLimits C] [PreservesFiniteLimits T]
    {A P : StructuredArrow S T}
    (f : P ⟶ A) [Mono f] : projectSubobject (Subobject.mk f) = Subobject.mk f.right :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `projectSubobject_factors` / 定理 `projectSubobject_factors`

English:
theorem projectSubobject_factors
  statement: [HasFiniteLimits C] [PreservesFiniteLimits T]
  proof: Subobject.ind _ fun P f hf =>
    ⟨P.hom ≫ T.map (Subobject.underlyingIso _).inv, by simp [← T.map_comp]⟩

中文:
定理 projectSubobject_factors
  结论: [有有限极限 C] [保持FiniteLimits T]
  证明: Subobject.ind _ fun P f hf =>
    ⟨P.hom ≫ T.map (Subobject.underlyingIso _).inv, by simp [← T.map_comp]⟩

Depends on / 依赖: P.hom, Subobject, Subobject.ind, Subobject.underlyingIso, T.map, T.map_comp, map_comp, underlyingIso
-/
theorem projectSubobject_factors [HasFiniteLimits C] [PreservesFiniteLimits T]
    {A : StructuredArrow S T} :
    forall P : Subobject A, exists q, q ≫ T.map (projectSubobject P).arrow = A.hom :=
  Subobject.ind _ fun P f hf =>
    ⟨P.hom ≫ T.map (Subobject.underlyingIso _).inv, by simp [← T.map_comp]⟩

set_option backward.isDefEq.respectTransparency false in
/-- A subobject of the underlying object of a structured arrow can be lifted to a subobject of
    the structured arrow, provided that there is a morphism making the subobject into a structured
    arrow. -/
@[simp]
/--
Definition of `liftSubobject` / `liftSubobject` 的定义

English:
definition liftSubobject
  signature: {A : StructuredArrow S T} (P : Subobject A.right) {q}
  body: Subobject.mk (homMk P.arrow hq : mk q ⟶ A)

中文:
定义 liftSubobject
  签名: {A : 结构化箭头 S T} (P : Subobject A.right) {q}
  定义体: Subobject.mk (homMk P.arrow hq : mk q ⟶ A)

Depends on / 依赖: P.arrow, Subobject, Subobject.mk
-/
def liftSubobject {A : StructuredArrow S T} (P : Subobject A.right) {q}
    (hq : q ≫ T.map P.arrow = A.hom) : Subobject A :=
  Subobject.mk (homMk P.arrow hq : mk q ⟶ A)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_projectSubobject` / 定理 `lift_projectSubobject`

English:
theorem lift_projectSubobject
  statement: [HasFiniteLimits C] [PreservesFiniteLimits T]
  proof: Subobject.ind _
    (by
      intro P f hf q hq
      fapply Subobject.mk_eq_mk_of_comm
      · fapply isoMk
        · exact Subobject.underlyingIso _
        · exact (cancel_mono (T.map f.right)).1 (by dsimp; simpa [← T.map_comp] using hq)
      · exact ext _ _ (by simp))

中文:
定理 lift_projectSubobject
  结论: [有有限极限 C] [保持FiniteLimits T]
  证明: Subobject.ind _
    (by
      intro P f hf q hq
      fapply Subobject.mk_eq_mk_of_comm
      · fapply isoMk
        · exact Subobject.underlyingIso _
        · exact (cancel_mono (T.map f.right)).1 (by dsimp; simpa [← T.map_comp] using hq)
      · exact ext _ _ (by simp))

Depends on / 依赖: Subobject, Subobject.ind, Subobject.mk_eq_mk_of_comm, Subobject.underlyingIso, T.map, T.map_comp, cancel_mono, f.right, fapply, map_comp, mk_eq_mk_of_comm, underlyingIso
-/
theorem lift_projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T]
    {A : StructuredArrow S T} :
    forall (P : Subobject A) {q} (hq : q ≫ T.map (projectSubobject P).arrow = A.hom),
      liftSubobject (projectSubobject P) hq = P :=
  Subobject.ind _
    (by
      intro P f hf q hq
      fapply Subobject.mk_eq_mk_of_comm
      · fapply isoMk
        · exact Subobject.underlyingIso _
        · exact (cancel_mono (T.map f.right)).1 (by dsimp; simpa [← T.map_comp] using hq)
      · exact ext _ _ (by simp))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `subobjectEquiv` / `subobjectEquiv` 的定义

English:
definition subobjectEquiv
  signature: [HasFiniteLimits C] [PreservesFiniteLimits T] (A : StructuredArrow S T)
  body: ⟨projectSubobject P, projectSubobject_factors P⟩
  invFun P := liftSubobject P.val P.prop.choose_spec
  left_inv _ := lift_projectSubobject _ _
  right_inv P := Subtype.ext (by simp only [liftSubobject, homMk_right, projectSubobject_mk,
      Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    intro P Q f g hf hg
    refine ⟨fun h => Subobject.mk_le_mk_of_comm ?_ ?_, fun h => ?_⟩
    · exact homMk (Subobject.ofMkLEMk _ _ h)
        ((cancel_mono (T.map g.right)).1 (by simp [← T.map_comp]))
    · simp
    · refine Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).right ?_
      exact congr_arg CommaMorphism.right (Subobject.ofMkLEMk_comp h)

中文:
定义 subobjectEquiv
  签名: [有有限极限 C] [保持FiniteLimits T] (A : 结构化箭头 S T)
  定义体: ⟨projectSubobject P, projectSubobject_factors P⟩
  invFun P := liftSubobject P.val P.prop.choose_spec
  left_inv _ := lift_projectSubobject _ _
  right_inv P := Subtype.ext (by simp only [liftSubobject, homMk_right, projectSubobject_mk,
      Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    intro P Q f g hf hg
    refine ⟨fun h => Subobject.mk_le_mk_of_comm ?_ ?_, fun h => ?_⟩
    · exact homMk (Subobject.ofMkLEMk _ _ h)
        ((cancel_mono (T.map g.right)).1 (by simp [← T.map_comp]))
    · simp
    · refine Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).right ?_
      exact congr_arg CommaMorphism.right (Subobject.ofMkLEMk_comp h)

Depends on / 依赖: projectSubobject, projectSubobject_factors
-/
def subobjectEquiv [HasFiniteLimits C] [PreservesFiniteLimits T] (A : StructuredArrow S T) :
    Subobject A ≃o { P : Subobject A.right // exists q, q ≫ T.map P.arrow = A.hom } where
  toFun P := ⟨projectSubobject P, projectSubobject_factors P⟩
  invFun P := liftSubobject P.val P.prop.choose_spec
  left_inv _ := lift_projectSubobject _ _
  right_inv P := Subtype.ext (by simp only [liftSubobject, homMk_right, projectSubobject_mk,
      Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    intro P Q f g hf hg
    refine ⟨fun h => Subobject.mk_le_mk_of_comm ?_ ?_, fun h => ?_⟩
    · exact homMk (Subobject.ofMkLEMk _ _ h)
        ((cancel_mono (T.map g.right)).1 (by simp [← T.map_comp]))
    · simp
    · refine Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).right ?_
      exact congr_arg CommaMorphism.right (Subobject.ofMkLEMk_comp h)

/--
Instance `wellPowered_structuredArrow` / 实例 `wellPowered_structuredArrow`

English:
instance wellPowered_structuredArrow
  signature: [LocallySmall.{w} C]
  body: small_map (subobjectEquiv X).toEquiv

中文:
实例 wellPowered_structuredArrow
  签名: [LocallySmall.{w} C]
  定义体: small_map (subobjectEquiv X).toEquiv

Depends on / 依赖: small_map, subobjectEquiv, toEquiv
-/
instance wellPowered_structuredArrow [LocallySmall.{w} C]
    [WellPowered.{w} C] [HasFiniteLimits C] [PreservesFiniteLimits T] :
    WellPowered.{w} (StructuredArrow S T) where
  subobject_small X := small_map (subobjectEquiv X).toEquiv

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

/--
Definition of `projectQuotient` / `projectQuotient` 的定义

English:
definition projectQuotient
  signature: [HasFiniteColimits C] [PreservesFiniteColimits S] {A : CostructuredArrow S T}
  body: by
  refine Subobject.lift (fun P f hf => Subobject.mk f.unop.left.op) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i.unop).op (Quiver.Hom.unop_inj ?_)
  have := congr_arg Quiver.Hom.unop hi
  simpa using! congr_arg CommaMorphism.left this

@[simp]

中文:
定义 projectQuotient
  签名: [有有限余极限 C] [保持FiniteColimits S] {A : CostructuredArrow S T}
  定义体: by
  refine Subobject.lift (fun P f hf => Subobject.mk f.unop.left.op) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i.unop).op (Quiver.Hom.unop_inj ?_)
  have := congr_arg Quiver.Hom.unop hi
  simpa using! congr_arg CommaMorphism.left this

@[simp]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, Quiver, Quiver.Hom.unop, Quiver.Hom.unop_inj, Subobject, Subobject.lift, Subobject.mk, Subobject.mk_eq_mk_of_comm, congr_arg, f.unop.left.op, i.unop, mapIso, mk_eq_mk_of_comm, unop_inj
-/
def projectQuotient [HasFiniteColimits C] [PreservesFiniteColimits S] {A : CostructuredArrow S T} :
    Subobject (op A) -> Subobject (op A.left) := by
  refine Subobject.lift (fun P f hf => Subobject.mk f.unop.left.op) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i.unop).op (Quiver.Hom.unop_inj ?_)
  have := congr_arg Quiver.Hom.unop hi
  simpa using! congr_arg CommaMorphism.left this

@[simp]
/--
theorem `projectQuotient_mk` / 定理 `projectQuotient_mk`

English:
theorem projectQuotient_mk
  statement: [HasFiniteColimits C] [PreservesFiniteColimits S]
  proof: rfl

中文:
定理 projectQuotient_mk
  结论: [有有限余极限 C] [保持FiniteColimits S]
  证明: rfl
-/
theorem projectQuotient_mk [HasFiniteColimits C] [PreservesFiniteColimits S]
    {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f] :
    projectQuotient (Subobject.mk f) = Subobject.mk f.unop.left.op :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `projectQuotient_factors` / 定理 `projectQuotient_factors`

English:
theorem projectQuotient_factors
  statement: [HasFiniteColimits C] [PreservesFiniteColimits S]
  proof: Subobject.ind _ fun P f hf =>
    ⟨S.map (Subobject.underlyingIso _).unop.inv ≫ P.unop.hom, by
      dsimp
      rw [← Category.assoc]; rw [← S.map_comp]; rw [← unop_comp]
      simp⟩

中文:
定理 projectQuotient_factors
  结论: [有有限余极限 C] [保持FiniteColimits S]
  证明: Subobject.ind _ fun P f hf =>
    ⟨S.map (Subobject.underlyingIso _).unop.inv ≫ P.unop.hom, by
      dsimp
      rw [← Category.assoc]; rw [← S.map_comp]; rw [← unop_comp]
      simp⟩

Depends on / 依赖: Category, Category.assoc, P.unop.hom, S.map, S.map_comp, Subobject, Subobject.ind, Subobject.underlyingIso, map_comp, underlyingIso, unop.inv, unop_comp
-/
theorem projectQuotient_factors [HasFiniteColimits C] [PreservesFiniteColimits S]
    {A : CostructuredArrow S T} :
    forall P : Subobject (op A), exists q, S.map (projectQuotient P).arrow.unop ≫ q = A.hom :=
  Subobject.ind _ fun P f hf =>
    ⟨S.map (Subobject.underlyingIso _).unop.inv ≫ P.unop.hom, by
      dsimp
      rw [← Category.assoc]; rw [← S.map_comp]; rw [← unop_comp]
      simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- A quotient of the underlying object of a costructured arrow can be lifted to a quotient of
    the costructured arrow, provided that there is a morphism making the quotient into a
    costructured arrow. -/
@[simp]
/--
Definition of `liftQuotient` / `liftQuotient` 的定义

English:
definition liftQuotient
  signature: {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q}
  body: Subobject.mk (homMk P.arrow.unop hq : A ⟶ mk q).op

中文:
定义 liftQuotient
  签名: {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q}
  定义体: Subobject.mk (homMk P.arrow.unop hq : A ⟶ mk q).op

Depends on / 依赖: P.arrow.unop, Subobject, Subobject.mk
-/
def liftQuotient {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q}
    (hq : S.map P.arrow.unop ≫ q = A.hom) : Subobject (op A) :=
  Subobject.mk (homMk P.arrow.unop hq : A ⟶ mk q).op

/-- Technical lemma for `lift_projectQuotient`. -/
@[simp]
/--
theorem `unop_left_comp_underlyingIso_hom_unop` / 定理 `unop_left_comp_underlyingIso_hom_unop`

English:
theorem unop_left_comp_underlyingIso_hom_unop
  statement: {A : CostructuredArrow S T}
  proof: by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op f.unop.left]
  rw [← unop_comp]; rw [Subobject.underlyingIso_hom_comp_eq_mk]

中文:
定理 unop_left_comp_underlyingIso_hom_unop
  结论: {A : CostructuredArrow S T}
  证明: by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op f.unop.left]
  rw [← unop_comp]; rw [Subobject.underlyingIso_hom_comp_eq_mk]

Depends on / 依赖: Quiver, Quiver.Hom.unop_op, Subobject, Subobject.underlyingIso_hom_comp_eq_mk, conv_lhs, f.unop.left, underlyingIso_hom_comp_eq_mk, unop_comp, unop_op
-/
theorem unop_left_comp_underlyingIso_hom_unop {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f.unop.left.op] :
    f.unop.left ≫ (Subobject.underlyingIso f.unop.left.op).hom.unop =
      (Subobject.mk f.unop.left.op).arrow.unop := by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op f.unop.left]
  rw [← unop_comp]; rw [Subobject.underlyingIso_hom_comp_eq_mk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_projectQuotient` / 定理 `lift_projectQuotient`

English:
theorem lift_projectQuotient
  statement: [HasFiniteColimits C] [PreservesFiniteColimits S]
  proof: Subobject.ind _
    (by
      intro P f hf q hq
      fapply Subobject.mk_eq_mk_of_comm
      · refine (Iso.op (isoMk ?_ ?_) : _ ≅ op (unop P))
        · exact (Subobject.underlyingIso f.unop.left.op).unop
        · refine (cancel_epi (S.map f.unop.left)).1 ?_
          simpa [← Category.assoc, ← S.map_comp] using hq
      · exact Quiver.Hom.unop_inj (by simp))

中文:
定理 lift_projectQuotient
  结论: [有有限余极限 C] [保持FiniteColimits S]
  证明: Subobject.ind _
    (by
      intro P f hf q hq
      fapply Subobject.mk_eq_mk_of_comm
      · refine (Iso.op (isoMk ?_ ?_) : _ ≅ op (unop P))
        · exact (Subobject.underlyingIso f.unop.left.op).unop
        · refine (cancel_epi (S.map f.unop.left)).1 ?_
          simpa [← Category.assoc, ← S.map_comp] using hq
      · exact Quiver.Hom.unop_inj (by simp))

Depends on / 依赖: Category, Category.assoc, Iso.op, Quiver, Quiver.Hom.unop_inj, S.map, S.map_comp, Subobject, Subobject.ind, Subobject.mk_eq_mk_of_comm, Subobject.underlyingIso, cancel_epi, f.unop.left, f.unop.left.op, fapply, map_comp, mk_eq_mk_of_comm, underlyingIso, unop_inj
-/
theorem lift_projectQuotient [HasFiniteColimits C] [PreservesFiniteColimits S]
    {A : CostructuredArrow S T} :
    forall (P : Subobject (op A)) {q} (hq : S.map (projectQuotient P).arrow.unop ≫ q = A.hom),
      liftQuotient (projectQuotient P) hq = P :=
  Subobject.ind _
    (by
      intro P f hf q hq
      fapply Subobject.mk_eq_mk_of_comm
      · refine (Iso.op (isoMk ?_ ?_) : _ ≅ op (unop P))
        · exact (Subobject.underlyingIso f.unop.left.op).unop
        · refine (cancel_epi (S.map f.unop.left)).1 ?_
          simpa [← Category.assoc, ← S.map_comp] using hq
      · exact Quiver.Hom.unop_inj (by simp))

/--
theorem `unop_left_comp_ofMkLEMk_unop` / 定理 `unop_left_comp_ofMkLEMk_unop`

English:
theorem unop_left_comp_ofMkLEMk_unop
  statement: {A : CostructuredArrow S T} {P Q : (CostructuredArrow S T)ᵒᵖ}
  proof: by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op g.unop.left]
  rw [← unop_comp]
  simp only [Subobject.ofMkLEMk_comp, Quiver.Hom.unop_op]

中文:
定理 unop_left_comp_ofMkLEMk_unop
  结论: {A : CostructuredArrow S T} {P Q : (CostructuredArrow S T)ᵒᵖ}
  证明: by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op g.unop.left]
  rw [← unop_comp]
  simp only [Subobject.ofMkLEMk_comp, Quiver.Hom.unop_op]

Depends on / 依赖: Quiver, Quiver.Hom.unop_op, Subobject, Subobject.ofMkLEMk_comp, conv_lhs, g.unop.left, ofMkLEMk_comp, unop_comp, unop_op
-/
theorem unop_left_comp_ofMkLEMk_unop {A : CostructuredArrow S T} {P Q : (CostructuredArrow S T)ᵒᵖ}
    {f : P ⟶ op A} {g : Q ⟶ op A} [Mono f.unop.left.op] [Mono g.unop.left.op]
    (h : Subobject.mk f.unop.left.op <= Subobject.mk g.unop.left.op) :
    g.unop.left ≫ (Subobject.ofMkLEMk f.unop.left.op g.unop.left.op h).unop = f.unop.left := by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op g.unop.left]
  rw [← unop_comp]
  simp only [Subobject.ofMkLEMk_comp, Quiver.Hom.unop_op]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `quotientEquiv` / `quotientEquiv` 的定义

English:
definition quotientEquiv
  signature: [HasFiniteColimits C] [PreservesFiniteColimits S] (A : CostructuredArrow S T)
  body: ⟨projectQuotient P, projectQuotient_factors P⟩
  invFun P := liftQuotient P.val P.prop.choose_spec
  left_inv _ := lift_projectQuotient _ _
  right_inv P := Subtype.ext (by simp only [liftQuotient, Quiver.Hom.unop_op, homMk_left,
      Quiver.Hom.op_unop, projectQuotient_mk, Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    intro P Q f g hf hg
    refine ⟨fun h => Subobject.mk_le_mk_of_comm ?_ ?_, fun h => ?_⟩
    · refine (homMk (Subobject.ofMkLEMk _ _ h).unop ((cancel_epi (S.map g.unop.left)).1 ?_)).op
      dsimp
      simp only [← S.map_comp_assoc, unop_left_comp_ofMkLEMk_unop, unop_op, CommaMorphism.w,
        right_eq_id, Functor.const_obj_map]
    · apply Quiver.Hom.unop_inj
      ext
      exact unop_left_comp_ofMkLEMk_unop _
    · refine Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).unop.left.op ?_
      refine Quiver.Hom.unop_inj ?_
      have := congr_arg Quiver.Hom.unop (Subobject.ofMkLEMk_comp h)
      simpa only [unop_op, Functor.id_obj, Functor.const_obj_obj, MonoOver.mk_obj, Over.mk_left,
        MonoOver.mk_arrow, unop_comp, Quiver.Hom.unop_op, comp_left]
          using congr_arg CommaMorphism.left this

中文:
定义 quotientEquiv
  签名: [有有限余极限 C] [保持FiniteColimits S] (A : CostructuredArrow S T)
  定义体: ⟨projectQuotient P, projectQuotient_factors P⟩
  invFun P := liftQuotient P.val P.prop.choose_spec
  left_inv _ := lift_projectQuotient _ _
  right_inv P := Subtype.ext (by simp only [liftQuotient, Quiver.Hom.unop_op, homMk_left,
      Quiver.Hom.op_unop, projectQuotient_mk, Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    intro P Q f g hf hg
    refine ⟨fun h => Subobject.mk_le_mk_of_comm ?_ ?_, fun h => ?_⟩
    · refine (homMk (Subobject.ofMkLEMk _ _ h).unop ((cancel_epi (S.map g.unop.left)).1 ?_)).op
      dsimp
      simp only [← S.map_comp_assoc, unop_left_comp_ofMkLEMk_unop, unop_op, CommaMorphism.w,
        right_eq_id, Functor.const_obj_map]
    · apply Quiver.Hom.unop_inj
      ext
      exact unop_left_comp_ofMkLEMk_unop _
    · refine Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).unop.left.op ?_
      refine Quiver.Hom.unop_inj ?_
      have := congr_arg Quiver.Hom.unop (Subobject.ofMkLEMk_comp h)
      simpa only [unop_op, Functor.id_obj, Functor.const_obj_obj, MonoOver.mk_obj, Over.mk_left,
        MonoOver.mk_arrow, unop_comp, Quiver.Hom.unop_op, comp_left]
          using congr_arg CommaMorphism.left this

Depends on / 依赖: projectQuotient, projectQuotient_factors
-/
def quotientEquiv [HasFiniteColimits C] [PreservesFiniteColimits S] (A : CostructuredArrow S T) :
    Subobject (op A) ≃o { P : Subobject (op A.left) // exists q, S.map P.arrow.unop ≫ q = A.hom } where
  toFun P := ⟨projectQuotient P, projectQuotient_factors P⟩
  invFun P := liftQuotient P.val P.prop.choose_spec
  left_inv _ := lift_projectQuotient _ _
  right_inv P := Subtype.ext (by simp only [liftQuotient, Quiver.Hom.unop_op, homMk_left,
      Quiver.Hom.op_unop, projectQuotient_mk, Subobject.mk_arrow])
  map_rel_iff' := by
    apply Subobject.ind₂
    intro P Q f g hf hg
    refine ⟨fun h => Subobject.mk_le_mk_of_comm ?_ ?_, fun h => ?_⟩
    · refine (homMk (Subobject.ofMkLEMk _ _ h).unop ((cancel_epi (S.map g.unop.left)).1 ?_)).op
      dsimp
      simp only [← S.map_comp_assoc, unop_left_comp_ofMkLEMk_unop, unop_op, CommaMorphism.w,
        right_eq_id, Functor.const_obj_map]
    · apply Quiver.Hom.unop_inj
      ext
      exact unop_left_comp_ofMkLEMk_unop _
    · refine Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk _ _ h).unop.left.op ?_
      refine Quiver.Hom.unop_inj ?_
      have := congr_arg Quiver.Hom.unop (Subobject.ofMkLEMk_comp h)
      simpa only [unop_op, Functor.id_obj, Functor.const_obj_obj, MonoOver.mk_obj, Over.mk_left,
        MonoOver.mk_arrow, unop_comp, Quiver.Hom.unop_op, comp_left]
          using congr_arg CommaMorphism.left this

/--
Instance `well_copowered_costructuredArrow` / 实例 `well_copowered_costructuredArrow`

English:
instance well_copowered_costructuredArrow
  signature: [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ]
  body: small_map (quotientEquiv (unop X)).toEquiv

中文:
实例 well_copowered_costructuredArrow
  签名: [LocallySmall.{w} C] [良幂.{w} Cᵒᵖ]
  定义体: small_map (quotientEquiv (unop X)).toEquiv

Depends on / 依赖: quotientEquiv, small_map, toEquiv
-/
instance well_copowered_costructuredArrow [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ]
    [HasFiniteColimits C] [PreservesFiniteColimits S] :
    WellPowered.{w} (CostructuredArrow S T)ᵒᵖ where
  subobject_small X := small_map (quotientEquiv (unop X)).toEquiv

end CostructuredArrow

end CategoryTheory
