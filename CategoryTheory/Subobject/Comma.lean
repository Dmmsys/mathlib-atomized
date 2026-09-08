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

/-- Every subobject of a structured arrow can be projected to a subobject of the underlying
    object. -/
/-
**CategoryTheory.StructuredArrow.projectSubobject** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.StructuredArrow`。
形式化陈述：projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T] {A : Struct
uredArrow S T} : Subobject A -> Subobject A.right
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every subobject of a structured arrow can be projected to a subobject of the und
erlying
    object.
-/
def projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T] {A : StructuredArrow S T} :
    Subobject A → Subobject A.right := by
  refine Subobject.lift (fun P f hf => Subobject.mk f.right) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) ?_
  exact congr_arg CommaMorphism.right hi

@[simp]
/-
**CategoryTheory.StructuredArrow.projectSubobject_mk** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.StructuredArrow`。
形式化陈述：projectSubobject_mk [HasFiniteLimits C] [PreservesFiniteLimits T] {A P : S
tructuredArrow S T} (f : P ⟶ A) [Mono f] : projectSubobject (Subobject.mk f) = S
ubobject.mk f.right
参数：f : P ⟶ A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projectSubobject_mk [HasFiniteLimits C] [PreservesFiniteLimits T]
    {A P : StructuredArrow S T}
    (f : P ⟶ A) [Mono f] : projectSubobject (Subobject.mk f) = Subobject.mk f.right :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.StructuredArrow.projectSubobject_factors** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：projectSubobject_factors [HasFiniteLimits C] [PreservesFiniteLimits T] {A 
: StructuredArrow S T} : forall P : Subobject A, exists q, q ≫ T.map (projectSub
object P).arrow = A.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projectSubobject_factors [HasFiniteLimits C] [PreservesFiniteLimits T]
    {A : StructuredArrow S T} :
    ∀ P : Subobject A, ∃ q, q ≫ T.map (projectSubobject P).arrow = A.hom :=
  Subobject.ind _ fun P f hf =>
    ⟨P.hom ≫ T.map (Subobject.underlyingIso _).inv, by simp [← T.map_comp]⟩

set_option backward.isDefEq.respectTransparency false in
/-- A subobject of the underlying object of a structured arrow can be lifted to a subobject of
    the structured arrow, provided that there is a morphism making the subobject into a structured
    arrow. -/
@[simp]
/-
**CategoryTheory.StructuredArrow.liftSubobject** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.StructuredArrow`。
形式化陈述：liftSubobject {A : StructuredArrow S T} (P : Subobject A.right) {q} (hq : 
q ≫ T.map P.arrow = A.hom) : Subobject A
参数：P : Subobject A.right；hq : q ≫ T.map P.arrow = A.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subobject of the underlying object of a structured arrow can be lifted to a su
bobject of
    the structured arrow, provided that there is a morphism making the subobject
 into a structured
    arrow.
-/
def liftSubobject {A : StructuredArrow S T} (P : Subobject A.right) {q}
    (hq : q ≫ T.map P.arrow = A.hom) : Subobject A :=
  Subobject.mk (homMk P.arrow hq : mk q ⟶ A)

set_option backward.isDefEq.respectTransparency false in
/-- Projecting and then lifting a subobject recovers the original subobject, because there is at
    most one morphism making the projected subobject into a structured arrow. -/
/-
**CategoryTheory.StructuredArrow.lift_projectSubobject** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.StructuredArrow`。
形式化陈述：lift_projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T] {A : S
tructuredArrow S T} : forall (P : Subobject A) {q} (hq : q ≫ T.map (projectSubob
ject P).arrow = A.hom), liftSubobject (projectSubobject P) hq = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `CategoryTheory.StructuredArrow.ext`：ext {A B : StructuredArrow S T} (f g
 : A ⟶ B) : f.right = g.right -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.StructuredArrow.isoMk_hom_right`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {S : D} {T : Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Projecting and then lifting a subobject recovers the original subobject, because
 there is at
    most one morphism making the projected subobject into a structured arrow.
-/
theorem lift_projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T]
    {A : StructuredArrow S T} :
    ∀ (P : Subobject A) {q} (hq : q ≫ T.map (projectSubobject P).arrow = A.hom),
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
/-- If `A : S → T.obj B` is a structured arrow for `S : D` and `T : C ⥤ D`, then we can explicitly
    describe the subobjects of `A` as the subobjects `P` of `B` in `C` for which `A.hom` factors
    through the image of `P` under `T`. -/
/-
**CategoryTheory.StructuredArrow.subobjectEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.StructuredArrow`。
形式化陈述：subobjectEquiv [HasFiniteLimits C] [PreservesFiniteLimits T] (A : Structur
edArrow S T) : Subobject A ≃o { P : Subobject A.right // exists q, q ≫ T.map P.a
rrow = A.hom } where toFun P
参数：A : StructuredArrow S T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.projectSubobject_factors`：projectSubobjec
t_factors [HasFiniteLimits C] [PreservesFiniteLimits T] {A : StructuredArrow S T
} : forall P : Subobject A, exists q, q ≫ T.m…

--- 原说明 ---
If `A : S → T.obj B` is a structured arrow for `S : D` and `T : C ⥤ D`, then we 
can explicitly
    describe the subobjects of `A` as the subobjects `P` of `B` in `C` for which
 `A.hom` factors
    through the image of `P` under `T`.
-/
def subobjectEquiv [HasFiniteLimits C] [PreservesFiniteLimits T] (A : StructuredArrow S T) :
    Subobject A ≃o { P : Subobject A.right // ∃ q, q ≫ T.map P.arrow = A.hom } where
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

/-- If `C` is well-powered and complete and `T` preserves limits, then `StructuredArrow S T` is
    well-powered. -/
/-
**CategoryTheory.StructuredArrow.wellPowered_structuredArrow** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：wellPowered_structuredArrow [LocallySmall.{w} C] [WellPowered.{w} C] [HasF
initeLimits C] [PreservesFiniteLimits T] : WellPowered.{w} (StructuredArrow S T)
 where subobject_small X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.locallySmall`：∀ {B : Type u₂} {T : Type u
₃} [inst : CategoryTheory.Category.{v₂, u₂} B] [inst_1 : CategoryTheory.Category
.{v₃, u₃} T]   (S : T) (T_1 : Cat…
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α

--- 原说明 ---
If `C` is well-powered and complete and `T` preserves limits, then `StructuredAr
row S T` is
    well-powered.
-/
instance wellPowered_structuredArrow [LocallySmall.{w} C]
    [WellPowered.{w} C] [HasFiniteLimits C] [PreservesFiniteLimits T] :
    WellPowered.{w} (StructuredArrow S T) where
  subobject_small X := small_map (subobjectEquiv X).toEquiv

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

/-- Every quotient of a costructured arrow can be projected to a quotient of the underlying
    object. -/
/-
**CategoryTheory.CostructuredArrow.projectQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.CostructuredArrow`。
形式化陈述：projectQuotient [HasFiniteColimits C] [PreservesFiniteColimits S] {A : Cos
tructuredArrow S T} : Subobject (op A) -> Subobject (op A.left)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every quotient of a costructured arrow can be projected to a quotient of the und
erlying
    object.
-/
def projectQuotient [HasFiniteColimits C] [PreservesFiniteColimits S] {A : CostructuredArrow S T} :
    Subobject (op A) → Subobject (op A.left) := by
  refine Subobject.lift (fun P f hf => Subobject.mk f.unop.left.op) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i.unop).op (Quiver.Hom.unop_inj ?_)
  have := congr_arg Quiver.Hom.unop hi
  simpa using! congr_arg CommaMorphism.left this

@[simp]
/-
**CategoryTheory.CostructuredArrow.projectQuotient_mk** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.CostructuredArrow`。
形式化陈述：projectQuotient_mk [HasFiniteColimits C] [PreservesFiniteColimits S] {A : 
CostructuredArrow S T} {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f] :
 projectQuotient (Subobject.mk f) = Subobject.mk f.unop.left.op
参数：CostructuredArrow S T；f : P ⟶ op A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projectQuotient_mk [HasFiniteColimits C] [PreservesFiniteColimits S]
    {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f] :
    projectQuotient (Subobject.mk f) = Subobject.mk f.unop.left.op :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CostructuredArrow.projectQuotient_factors** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：projectQuotient_factors [HasFiniteColimits C] [PreservesFiniteColimits S] 
{A : CostructuredArrow S T} : forall P : Subobject (op A), exists q, S.map (proj
ectQuotient P).arrow.unop ≫ q = A.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `CategoryTheory.op_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {A B : C} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryTheor
y.Mono f.op
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projectQuotient_factors [HasFiniteColimits C] [PreservesFiniteColimits S]
    {A : CostructuredArrow S T} :
    ∀ P : Subobject (op A), ∃ q, S.map (projectQuotient P).arrow.unop ≫ q = A.hom :=
  Subobject.ind _ fun P f hf =>
    ⟨S.map (Subobject.underlyingIso _).unop.inv ≫ P.unop.hom, by
      dsimp
      rw [← Category.assoc, ← S.map_comp, ← unop_comp]
      simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- A quotient of the underlying object of a costructured arrow can be lifted to a quotient of
    the costructured arrow, provided that there is a morphism making the quotient into a
    costructured arrow. -/
@[simp]
/-
**CategoryTheory.CostructuredArrow.liftQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.CostructuredArrow`。
形式化陈述：liftQuotient {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q} (
hq : S.map P.arrow.unop ≫ q = A.hom) : Subobject (op A)
参数：P : Subobject (op A.left)；hq : S.map P.arrow.unop ≫ q = A.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quotient of the underlying object of a costructured arrow can be lifted to a q
uotient of
    the costructured arrow, provided that there is a morphism making the quotien
t into a
    costructured arrow.
-/
def liftQuotient {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q}
    (hq : S.map P.arrow.unop ≫ q = A.hom) : Subobject (op A) :=
  Subobject.mk (homMk P.arrow.unop hq : A ⟶ mk q).op

/-- Technical lemma for `lift_projectQuotient`. -/
@[simp]
/-
**CategoryTheory.CostructuredArrow.unop_left_comp_underlyingIso_hom_unop** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：unop_left_comp_underlyingIso_hom_unop {A : CostructuredArrow S T} {P : (Co
structuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f.unop.left.op] : f.unop.left ≫ (Su
bobject.underlyingIso f.unop.left.op).hom.unop = (Subobject.mk f.unop.left.op).a
rrow.unop
参数：CostructuredArrow S T；f : P ⟶ op A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow

--- 原说明 ---
Technical lemma for `lift_projectQuotient`.
-/
theorem unop_left_comp_underlyingIso_hom_unop {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f.unop.left.op] :
    f.unop.left ≫ (Subobject.underlyingIso f.unop.left.op).hom.unop =
      (Subobject.mk f.unop.left.op).arrow.unop := by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op f.unop.left]
  rw [← unop_comp, Subobject.underlyingIso_hom_comp_eq_mk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Projecting and then lifting a quotient recovers the original quotient, because there is at most
    one morphism making the projected quotient into a costructured arrow. -/
/-
**CategoryTheory.CostructuredArrow.lift_projectQuotient** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.CostructuredArrow`。
形式化陈述：lift_projectQuotient [HasFiniteColimits C] [PreservesFiniteColimits S] {A 
: CostructuredArrow S T} : forall (P : Subobject (op A)) {q} (hq : S.map (projec
tQuotient P).arrow.unop ≫ q = A.hom), liftQuotient (projectQuotient P) hq = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `CategoryTheory.op_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {A B : C} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryTheor
y.Mono f.op
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.CostructuredArrow.unop_left_comp_underlyingIso_hom_unop`：
unop_left_comp_underlyingIso_hom_unop {A : CostructuredArrow S T} {P : (Costruct
uredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f.unop.left.op] : f.u…
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Projecting and then lifting a quotient recovers the original quotient, because t
here is at most
    one morphism making the projected quotient into a costructured arrow.
-/
theorem lift_projectQuotient [HasFiniteColimits C] [PreservesFiniteColimits S]
    {A : CostructuredArrow S T} :
    ∀ (P : Subobject (op A)) {q} (hq : S.map (projectQuotient P).arrow.unop ≫ q = A.hom),
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

/-- Technical lemma for `quotientEquiv`. -/
/-
**CategoryTheory.CostructuredArrow.unop_left_comp_ofMkLEMk_unop** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：unop_left_comp_ofMkLEMk_unop {A : CostructuredArrow S T} {P Q : (Costructu
redArrow S T)ᵒᵖ} {f : P ⟶ op A} {g : Q ⟶ op A} [Mono f.unop.left.op] [Mono g.uno
p.left.op] (h : Subobject.mk f.unop.left.op <= Subobject.mk g.unop.left.op) : g.
unop.left ≫ (Subobject.ofMkLEMk f.unop.left.op g.unop.left.op h).unop = f.unop.l
eft
参数：CostructuredArrow S T；h : Subobject.mk f.unop.left.op <= Subobject.mk g.unop.
left.op。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.Hom.unop_op`：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop
 = f
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Technical lemma for `quotientEquiv`.
-/
theorem unop_left_comp_ofMkLEMk_unop {A : CostructuredArrow S T} {P Q : (CostructuredArrow S T)ᵒᵖ}
    {f : P ⟶ op A} {g : Q ⟶ op A} [Mono f.unop.left.op] [Mono g.unop.left.op]
    (h : Subobject.mk f.unop.left.op ≤ Subobject.mk g.unop.left.op) :
    g.unop.left ≫ (Subobject.ofMkLEMk f.unop.left.op g.unop.left.op h).unop = f.unop.left := by
  conv_lhs =>
    congr
    rw [← Quiver.Hom.unop_op g.unop.left]
  rw [← unop_comp]
  simp only [Subobject.ofMkLEMk_comp, Quiver.Hom.unop_op]

set_option backward.isDefEq.respectTransparency false in
/-- If `A : S.obj B ⟶ T` is a costructured arrow for `S : C ⥤ D` and `T : D`, then we can
    explicitly describe the quotients of `A` as the quotients `P` of `B` in `C` for which `A.hom`
    factors through the image of `P` under `S`. -/
/-
**CategoryTheory.CostructuredArrow.quotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.CostructuredArrow`。
形式化陈述：quotientEquiv [HasFiniteColimits C] [PreservesFiniteColimits S] (A : Costr
ucturedArrow S T) : Subobject (op A) ≃o { P : Subobject (op A.left) // exists q,
 S.map P.arrow.unop ≫ q = A.hom } where toFun P
参数：A : CostructuredArrow S T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.projectQuotient_factors`：projectQuotien
t_factors [HasFiniteColimits C] [PreservesFiniteColimits S] {A : CostructuredArr
ow S T} : forall P : Subobject (op A), exists …

--- 原说明 ---
If `A : S.obj B ⟶ T` is a costructured arrow for `S : C ⥤ D` and `T : D`, then w
e can
    explicitly describe the quotients of `A` as the quotients `P` of `B` in `C` 
for which `A.hom`
    factors through the image of `P` under `S`.
-/
def quotientEquiv [HasFiniteColimits C] [PreservesFiniteColimits S] (A : CostructuredArrow S T) :
    Subobject (op A) ≃o { P : Subobject (op A.left) // ∃ q, S.map P.arrow.unop ≫ q = A.hom } where
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

/-- If `C` is well-copowered and cocomplete and `S` preserves colimits, then
    `CostructuredArrow S T` is well-copowered. -/
/-
**CategoryTheory.CostructuredArrow.well_copowered_costructuredArrow** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：well_copowered_costructuredArrow [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ
] [HasFiniteColimits C] [PreservesFiniteColimits S] : WellPowered.{w} (Costructu
redArrow S T)ᵒᵖ where subobject_small X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.CostructuredArrow.locallySmall`：∀ {A : Type u₁} {T : Type
 u₃} [inst : CategoryTheory.Category.{v₁, u₁} A] [inst_1 : CategoryTheory.Catego
ry.{v₃, u₃} T]   (S : CategoryTheor…
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α

--- 原说明 ---
If `C` is well-copowered and cocomplete and `S` preserves colimits, then
    `CostructuredArrow S T` is well-copowered.
-/
instance well_copowered_costructuredArrow [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ]
    [HasFiniteColimits C] [PreservesFiniteColimits S] :
    WellPowered.{w} (CostructuredArrow S T)ᵒᵖ where
  subobject_small X := small_map (quotientEquiv (unop X)).toEquiv

end CostructuredArrow

end CategoryTheory

