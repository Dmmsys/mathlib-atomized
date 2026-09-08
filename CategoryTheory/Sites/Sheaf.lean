/-
Copyright (c) 2020 Kevin Buzzard, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal

/-!
# Sheaves taking values in a category

If C is a category with a Grothendieck topology, we define the notion of a sheaf taking values in
an arbitrary category `A`. We follow the definition in https://stacks.math.columbia.edu/tag/00VR,
noting that the presheaf of sets "defined above" can be seen in the comments between tags 00VQ and
00VR on the page <https://stacks.math.columbia.edu/tag/00VL>. The advantage of this definition is
that we need no assumptions whatsoever on `A` other than the assumption that the morphisms in `C`
and `A` live in the same universe.

* An `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is defined to be a sheaf (for the topology `J`) iff for
  every `E : A`, the type-valued presheaves of sets given by sending `U : Cᵒᵖ` to `Hom_{A}(E, P U)`
  are all sheaves of sets, see `CategoryTheory.Presheaf.IsSheaf`.
* When `A = Type`, this recovers the basic definition of sheaves of sets, see
  `CategoryTheory.isSheaf_iff_isSheaf_of_type`.
* An alternate definition in terms of limits, unconditionally equivalent to the original one:
  see `CategoryTheory.Presheaf.isSheaf_iff_isLimit`.
* An alternate definition when `C` is small, has pullbacks and `A` has products is given by an
  equalizer condition `CategoryTheory.Presheaf.IsSheaf'`. This is equivalent to the earlier
  definition, shown in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
* When `A = Type`, this is *definitionally* equal to the equalizer condition for presieves in
  `CategoryTheory.Sites.SheafOfTypes`.
* When `A` has limits and there is a functor `s : A ⥤ Type` which is faithful, reflects isomorphisms
  and preserves limits, then `P : Cᵒᵖ ⥤ A` is a sheaf iff the underlying presheaf of types
  `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf (`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`).
  Cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's
  only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which
  additionally assumes filtered colimits.

## Implementation notes

Occasionally we need to take a limit in `A` of a collection of morphisms of `C` indexed
by a collection of objects in `C`. This turns out to force the morphisms of `A` to be
in a sufficiently large universe. Rather than use `UnivLE` we prove some results for
a category `A'` instead, whose morphism universe of `A'` is defined to be `max u₁ v₁`, where
`u₁, v₁` are the universes for `C`. Perhaps after we get better at handling universe
inequalities this can be changed.

-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)

-- We follow https://stacks.math.columbia.edu/tag/00VL definition 00VR
/-- A sheaf of A is a presheaf `P : Cᵒᵖ ⥤ A` such that for every `E : A`, the
presheaf of types given by sending `U : C` to `Hom_{A}(E, P U)` is a sheaf of types. -/
@[stacks 00VR]
/-
**CategoryTheory.Presheaf.IsSheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pres
heaf`。
形式化陈述：IsSheaf (P : Cᵒᵖ ⥤ A) : Prop
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf of A is a presheaf `P : Cᵒᵖ ⥤ A` such that for every `E : A`, the
presheaf of types given by sending `U : C` to `Hom_{A}(E, P U)` is a sheaf of ty
pes.
-/
def IsSheaf (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))

/-- Condition that a presheaf with values in a concrete category is separated for
a Grothendieck topology. -/
/-
**CategoryTheory.Presheaf.IsSeparated** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Presheaf`。
形式化陈述：IsSeparated (P : Cᵒᵖ ⥤ A) {FA : A -> A -> Type*} {CA : A -> Type*} [forall
 X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] : Prop
参数：P : Cᵒᵖ ⥤ A；FA X Y；CA X；CA Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Condition that a presheaf with values in a concrete category is separated for
a Grothendieck topology.
-/
def IsSeparated (P : Cᵒᵖ ⥤ A) {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] : Prop :=
  ∀ (X : C) (S : Sieve X) (_ : S ∈ J X) (x y : ToType (P.obj (op X))),
    (∀ (Y : C) (f : Y ⟶ X) (_ : S f), P.map f.op x = P.map f.op y) → x = y

section LimitSheafCondition

open Presieve Presieve.FamilyOfElements Limits

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : Sieve X) (R : Presieve X) (E : Aᵒᵖ)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a sieve `S` on `X : C`, a presheaf `P : Cᵒᵖ ⥤ A`, and an object `E` of `A`,
    the cones over the natural diagram `S.arrows.diagram.op ⋙ P` associated to `S` and `P`
    with cone point `E` are in 1-1 correspondence with `SieveCompatible` family of elements
    for the sieve `S` and the presheaf of types `Hom (E, P -)`. -/
/-
**CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：conesEquivSieveCompatibleFamily : (S.arrows.diagram.op ⋙ P).cones.obj E ≃ 
{ x : FamilyOfElements (P ⋙ coyoneda.obj E) (S : Presieve X) // x.SieveCompatibl
e } where toFun π
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sieve `S` on `X : C`, a presheaf `P : Cᵒᵖ ⥤ A`, and an object `E` of `A`
,
    the cones over the natural diagram `S.arrows.diagram.op ⋙ P` associated to `
S` and `P`
    with cone point `E` are in 1-1 correspondence with `SieveCompatible` family 
of elements
    for the sieve `S` and the presheaf of types `Hom (E, P -)`.
-/
def conesEquivSieveCompatibleFamily :
    (S.arrows.diagram.op ⋙ P).cones.obj E ≃
      { x : FamilyOfElements (P ⋙ coyoneda.obj E) (S : Presieve X) // x.SieveCompatible } where
  toFun π :=
    ⟨fun _ f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      let φ : S.arrows.categoryMk (g ≫ f) (S.downward_closed hf g) ⟶
        S.arrows.categoryMk f hf := ObjectProperty.homMk (Over.homMk _ rfl)
      simpa using! π.naturality φ.op⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        have := x.2 f.unop.1.hom g.unop.hom.left f.unop.2
        dsimp at this ⊢
        rw [id_comp, ← this]
        convert! rfl
        simp only [Over.w] }

variable {P S E}
variable {x : FamilyOfElements (P ⋙ coyoneda.obj E) S.arrows} (hx : SieveCompatible x)

/-- The cone corresponding to a `SieveCompatible` family of elements, dot notation enabled. -/
@[simp]
/-
**CategoryTheory.Presheaf._root_.CategoryTheory.Presieve.FamilyOfElements.SieveC
ompatible.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone corresponding to a `SieveCompatible` family of elements, dot notation e
nabled.
-/
def _root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone :
    Cone (S.arrows.diagram.op ⋙ P) where
  pt := E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩

/-- Cone morphisms from the cone corresponding to a `SieveCompatible` family to the natural
    cone associated to a sieve `S` and a presheaf `P` are in 1-1 correspondence with amalgamations
    of the family. -/
/-
**CategoryTheory.Presheaf.homEquivAmalgamation** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Presheaf`。
形式化陈述：homEquivAmalgamation : (hx.cone ⟶ P.mapCone S.arrows.cocone.op) ≃ { t // x
.IsAmalgamation t } where toFun l
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cone morphisms from the cone corresponding to a `SieveCompatible` family to the 
natural
    cone associated to a sieve `S` and a presheaf `P` are in 1-1 correspondence 
with amalgamations
    of the family.
-/
def homEquivAmalgamation :
    (hx.cone ⟶ P.mapCone S.arrows.cocone.op) ≃ { t // x.IsAmalgamation t } where
  toFun l := ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩

variable (P S)

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone is a limit cone
    iff `Hom (E, P -)` is a sheaf of types for the sieve `S` and all `E : A`. -/
/-
**CategoryTheory.Presheaf.isLimit_iff_isSheafFor** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Presheaf`。
形式化陈述：isLimit_iff_isSheafFor : Nonempty (IsLimit (P.mapCone S.arrows.cocone.op))
 ↔ forall E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) S.arrows
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Classical.nonempty_pi`：Classical.nonempty_pi {ι} {α : ι -> Sort*} : None
mpty (forall i, α i) ↔ forall i, Nonempty (α i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `unique_subtype_iff_existsUnique`：unique_subtype_iff_existsUnique {α} (p 
: α -> Prop) : Nonempty (Unique (Subtype p)) ↔ exists! a, p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone is a l
imit cone
    iff `Hom (E, P -)` is a sheaf of types for the sieve `S` and all `E : A`.
-/
theorem isLimit_iff_isSheafFor :
    Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) S.arrows := by
  dsimp [IsSheafFor]; simp_rw [compatible_iff_sieveCompatible]
  rw [((Cone.isLimitEquivIsTerminal _).trans (isTerminalEquivUnique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    rw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_existsUnique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_existsUnique]
    exact h _ _ (eqv π).2

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone admits at most one
    morphism from every cone in the same category (i.e. over the same diagram),
    iff `Hom (E, P -)` is separated for the sieve `S` and all `E : A`. -/
/-
**CategoryTheory.Presheaf.subsingleton_iff_isSeparatedFor** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：subsingleton_iff_isSeparatedFor : (forall c, Subsingleton (c ⟶ P.mapCone S
.arrows.cocone.op)) ↔ forall E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda.obj E) S.arro
ws
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.is_compatible_of_exists_amalgamation`：is_compati
ble_of_exists_amalgamation (x : FamilyOfElements P R) (h : exists t, x.IsAmalgam
ation t) : x.Compatible
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.compatible_iff_sieveCompatible`：compatible_iff_s
ieveCompatible (x : FamilyOfElements P (S : Presieve X)) : x.Compatible ↔ x.Siev
eCompatible
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone admits
 at most one
    morphism from every cone in the same category (i.e. over the same diagram),
    iff `Hom (E, P -)` is separated for the sieve `S` and all `E : A`.
-/
theorem subsingleton_iff_isSeparatedFor :
    (∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda.obj E) S.arrows := by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieveCompatible] at hx
    specialize hs hx.cone
    rcases hs with ⟨hs⟩
    simpa only [Subtype.mk.injEq] using (show Subtype.mk t₁ h₁ = ⟨t₂, h₂⟩ from
      (homEquivAmalgamation hx).symm.injective (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := homEquivAmalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2

/-- A presheaf `P` is a sheaf for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` is a limit cone. -/
/-
**CategoryTheory.Presheaf.isSheaf_iff_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Presheaf`。
形式化陈述：isSheaf_iff_isLimit : IsSheaf J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X
 -> Nonempty (IsLimit (P.mapCone S.arrows.cocone.op))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presheaf.isLimit_iff_isSheafFor`：isLimit_iff_isSheafFor :
 Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) ↔ forall E : Aᵒᵖ, IsSheafFor 
(P ⋙ coyoneda.obj E) S.arrows
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
A presheaf `P` is a sheaf for the Grothendieck topology `J` iff for every coveri
ng sieve
    `S` of `J`, the natural cone associated to `P` and `S` is a limit cone.
-/
theorem isSheaf_iff_isLimit :
    IsSheaf J P ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) :=
  ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩

/-- A presheaf `P` is separated for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` admits at most one morphism from every
    cone in the same category. -/
/-
**CategoryTheory.Presheaf.isSeparated_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：isSeparated_iff_subsingleton : (forall E : A, Presieve.IsSeparated J (P ⋙ 
coyoneda.obj (op E))) ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> forall c, Subs
ingleton (c ⟶ P.mapCone S.arrows.cocone.op)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presheaf.subsingleton_iff_isSeparatedFor`：subsingleton_if
f_isSeparatedFor : (forall c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op)) ↔
 forall E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
A presheaf `P` is separated for the Grothendieck topology `J` iff for every cove
ring sieve
    `S` of `J`, the natural cone associated to `P` and `S` admits at most one mo
rphism from every
    cone in the same category.
-/
theorem isSeparated_iff_subsingleton :
    (∀ E : A, Presieve.IsSeparated J (P ⋙ coyoneda.obj (op E))) ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op) :=
  ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩

/-- Given presieve `R` and presheaf `P : Cᵒᵖ ⥤ A`, the natural cone associated to `P` and
    the sieve `Sieve.generate R` generated by `R` is a limit cone iff `Hom (E, P -)` is a
    sheaf of types for the presieve `R` and all `E : A`. -/
/-
**CategoryTheory.Presheaf.isLimit_iff_isSheafFor_presieve** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLimit_iff_isSheafFor_presieve : Nonempty (IsLimit (P.mapCone (generate R
).arrows.cocone.op)) ↔ forall E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Presheaf.isLimit_iff_isSheafFor`：isLimit_iff_isSheafFor :
 Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) ↔ forall E : Aᵒᵖ, IsSheafFor 
(P ⋙ coyoneda.obj E) S.arrows
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)

--- 原说明 ---
Given presieve `R` and presheaf `P : Cᵒᵖ ⥤ A`, the natural cone associated to `P
` and
    the sieve `Sieve.generate R` generated by `R` is a limit cone iff `Hom (E, P
 -)` is a
    sheaf of types for the presieve `R` and all `E : A`.
-/
theorem isLimit_iff_isSheafFor_presieve :
    Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R :=
  (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)

/-- A presheaf `P` is a sheaf for the Grothendieck topology generated by a pretopology `K`
    iff for every covering presieve `R` of `K`, the natural cone associated to `P` and
    `Sieve.generate R` is a limit cone. -/
/-
**CategoryTheory.Presheaf.isSheaf_iff_isLimit_pretopology** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) : IsS
heaf K.toGrothendieck P ↔ forall ⦃X : C⦄ (R : Presieve X), R in K X -> Nonempty 
(IsLimit (P.mapCone (generate R).arrows.cocone.op))
参数：K : Pretopology C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presheaf.isLimit_iff_isSheafFor_presieve`：isLimit_iff_isS
heafFor_presieve : Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) 
↔ forall E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.ob…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
A presheaf `P` is a sheaf for the Grothendieck topology generated by a pretopolo
gy `K`
    iff for every covering presieve `R` of `K`, the natural cone associated to `
P` and
    `Sieve.generate R` is a limit cone.
-/
theorem isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf K.toGrothendieck P ↔
      ∀ ⦃X : C⦄ (R : Presieve X),
        R ∈ K X → Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) := by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩

end LimitSheafCondition

variable {J}

/-- This is a wrapper around `Presieve.IsSheafFor.amalgamate` to be used below.
  If `P` is a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalgamate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`. -/
/-
**CategoryTheory.Presheaf.IsSheaf.amalgamate** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Presheaf.IsSheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] →           {E : A} →             {X : C} → 
              {P : CategoryTheory.Functor Cᵒᵖ A} →                 CategoryTheor
y.Presheaf.IsSheaf J P →                   (S : J.Cover X) →                    
 (x : (I : S.Arrow) → E ⟶ P.obj (Opposite.op I.Y)) →                       (∀ ⦃I
₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),                           CategoryTheory.C
ategoryStruct.comp (x I₁) (P.map r.g₁.op) =                             Category
Theory.CategoryStruct.comp (x I₂) (P.map r.g₂.op)) →                         (E 
⟶ P.obj (Opposite.op X))
参数：S : J.Cover X；x : (I : S.Arrow) → E ⟶ P.obj (Opposite.op I.Y)；∀ ⦃I₁ I₂ : S.Ar
row⦄ (r : I₁.Relation I₂),                           CategoryTheory.CategoryStru
ct.comp (x I₁) (P.map r.g₁.op) =                             CategoryTheory.Cate
goryStruct.comp (x I₂) (P.map r.g₂.op)；E ⟶ P.obj (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a wrapper around `Presieve.IsSheafFor.amalgamate` to be used below.
  If `P` is a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms
 from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalg
amate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`.
-/
def IsSheaf.amalgamate {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun _ _ _ _ _ _ _ h₁ h₂ w =>
    @hx { hf := h₁, .. } { hf := h₂, .. } { w := w, .. }

@[reassoc (attr := simp)]
/-
**CategoryTheory.Presheaf.IsSheaf.amalgamate_map** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {E : A} {X : C} {P : CategoryTheory.Functor Cᵒᵖ A}   (hP : CategoryT
heory.Presheaf.IsSheaf J P) (S : J.Cover X) (x : (I : S.Arrow) → E ⟶ P.obj (Oppo
site.op I.Y))   (hx :     ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),       Catego
ryTheory.CategoryStruct.comp (x I₁) (P.map r.g₁.op) =         CategoryTheory.Cat
egoryStruct.comp (x I₂) (P.map r.g₂.op))   (I : S.Arrow), CategoryTheory.Categor
yStruct.comp (hP.amalgamate S x hx) (P.map I.f.op) = x I
参数：hP : CategoryTheory.Presheaf.IsSheaf J P；S : J.Cover X；x : (I : S.Arrow) → E 
⟶ P.obj (Opposite.op I.Y)；hx :     ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),    
   CategoryTheory.CategoryStruct.comp (x I₁) (P.map r.g₁.op) =         CategoryT
heory.CategoryStruct.comp (x I₂) (P.map r.g₂.op)；I : S.Arrow；hP.amalgamate S x h
x；P.map I.f.op。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.condition`：condition (S : J.Co
ver X) : (S : Sieve X) in J X
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
-/
theorem IsSheaf.amalgamate_map {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op)
    (I : S.Arrow) :
    hP.amalgamate S x hx ≫ P.map I.f.op = x _ := by
  apply (hP _ _ S.condition).valid_glue
/-
**CategoryTheory.Presheaf.IsSheaf.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {E : A} {X : C} {P : CategoryTheory.Functor Cᵒᵖ A},   CategoryTheory
.Presheaf.IsSheaf J P →     ∀ (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (Opposite.op X)
),       (∀ (I : S.Arrow),           CategoryTheory.CategoryStruct.comp e₁ (P.ma
p I.f.op) = CategoryTheory.CategoryStruct.comp e₂ (P.map I.f.op)) →         e₁ =
 e₂
参数：S : J.Cover X；e₁ e₂ : E ⟶ P.obj (Opposite.op X)；∀ (I : S.Arrow),           Ca
tegoryTheory.CategoryStruct.comp e₁ (P.map I.f.op) = CategoryTheory.CategoryStru
ct.comp e₂ (P.map I.f.op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.condition`：condition (S : J.Co
ver X) : (S : Sieve X) in J X
-/
theorem IsSheaf.hom_ext {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : ∀ I : S.Arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩
/-
**CategoryTheory.Presheaf.IsSheaf.hom_ext_ofArrows** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheory.Grothendieck
Topology C} {P : CategoryTheory.Functor Cᵒᵖ A},   CategoryTheory.Presheaf.IsShea
f J P →     ∀ {I : Type u_1} {S : C} {X : I → C} (f : (i : I) → X i ⟶ S),       
CategoryTheory.Sieve.ofArrows X f ∈ J S →         ∀ {E : A} {x y : E ⟶ P.obj (Op
posite.op S)},           (∀ (i : I),               CategoryTheory.CategoryStruct
.comp x (P.map (f i).op) =                 CategoryTheory.CategoryStruct.comp y 
(P.map (f i).op)) →             x = y
参数：f : (i : I) → X i ⟶ S；Opposite.op S；∀ (i : I),               CategoryTheory.C
ategoryStruct.comp x (P.map (f i).op) =                 CategoryTheory.CategoryS
truct.comp y (P.map (f i).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma IsSheaf.hom_ext_ofArrows
    {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I → C}
    (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) {E : A}
    {x y : E ⟶ P.obj (op S)} (h : ∀ i, x ≫ P.map (f i).op = y ≫ P.map (f i).op) :
    x = y := by
  apply hP.hom_ext ⟨_, hf⟩
  rintro ⟨Z, _, _, g, _, ⟨i⟩, rfl⟩
  dsimp
  rw [P.map_comp, reassoc_of% (h i)]

section

variable {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I → C}
  (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) {E : A}
  (x : ∀ i, E ⟶ P.obj (op (X i)))
  (hx : ∀ ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),
    a ≫ f i = b ≫ f j → x i ≫ P.map a.op = x j ≫ P.map b.op)
include hP hf hx

/-
**CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheory.Grothendieck
Topology C} {P : CategoryTheory.Functor Cᵒᵖ A},   CategoryTheory.Presheaf.IsShea
f J P →     ∀ {I : Type u_1} {S : C} {X : I → C} (f : (i : I) → X i ⟶ S),       
CategoryTheory.Sieve.ofArrows X f ∈ J S →         ∀ {E : A} (x : (i : I) → E ⟶ P
.obj (Opposite.op (X i))),           (∀ ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶
 X j),               CategoryTheory.CategoryStruct.comp a (f i) = CategoryTheory
.CategoryStruct.comp b (f j) →                 CategoryTheory.CategoryStruct.com
p (x i) (P.map a.op) =                   CategoryTheory.CategoryStruct.comp (x j
) (P.map b.op)) →             ∃! g, ∀ (i : I), CategoryTheory.CategoryStruct.com
p g (P.map (f i).op) = x i
参数：f : (i : I) → X i ⟶ S；x : (i : I) → E ⟶ P.obj (Opposite.op (X i))；∀ ⦃W : C⦄ ⦃
i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),               CategoryTheory.CategoryStruc
t.comp a (f i) = CategoryTheory.CategoryStruct.comp b (f j) →                 Ca
tegoryTheory.CategoryStruct.comp (x i) (P.map a.op) =                   Category
Theory.CategoryStruct.comp (x j) (P.map b.op)；i : I；P.map (f i).op。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presieve.isSheafFor_arrows_iff`：isSheafFor_arrows_iff : (
ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I) -> P.obj (op (X i))), Arrows.C
ompatible P π x -> exists! t, foral…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
-/
lemma IsSheaf.existsUnique_amalgamation_ofArrows :
    ∃! (g : E ⟶ P.obj (op S)), ∀ (i : I), g ≫ P.map (f i).op = x i :=
  (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)

/-- If `P : Cᵒᵖ ⥤ A` is a sheaf and `f i : X i ⟶ S` is a covering family, then
a morphism `E ⟶ P.obj (op S)` can be constructed from a compatible family of
morphisms `x : E ⟶ P.obj (op (X i))`. -/
/-
**CategoryTheory.Presheaf.IsSheaf.amalgamateOfArrows** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Presheaf.IsSheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {A : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} A] →         {J : Cat
egoryTheory.GrothendieckTopology C} →           {P : CategoryTheory.Functor Cᵒᵖ 
A} →             CategoryTheory.Presheaf.IsSheaf J P →               {I : Type u
_1} →                 {S : C} →                   {X : I → C} →                 
    (f : (i : I) → X i ⟶ S) →                       CategoryTheory.Sieve.ofArrow
s X f ∈ J S →                         {E : A} →                           (x : (
i : I) → E ⟶ P.obj (Opposite.op (X i))) →                             (∀ ⦃W : C⦄
 ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),                                 Category
Theory.CategoryStruct.comp a (f i) =                                     Categor
yTheory.CategoryStruct.comp b (f j) →                                   Category
Theory.CategoryStruct.comp (x i) (P.map a.op) =                                 
    CategoryTheory.CategoryStruct.comp (x j) (P.map b.op)) →                    
           (E ⟶ P.obj (Opposite.op S))
参数：f : (i : I) → X i ⟶ S；x : (i : I) → E ⟶ P.obj (Opposite.op (X i))；∀ ⦃W : C⦄ ⦃
i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),                                 CategoryTh
eory.CategoryStruct.comp a (f i) =                                     CategoryT
heory.CategoryStruct.comp b (f j) →                                   CategoryTh
eory.CategoryStruct.comp (x i) (P.map a.op) =                                   
  CategoryTheory.CategoryStruct.comp (x j) (P.map b.op)；E ⟶ P.obj (Opposite.op S
)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheor…

--- 原说明 ---
If `P : Cᵒᵖ ⥤ A` is a sheaf and `f i : X i ⟶ S` is a covering family, then
a morphism `E ⟶ P.obj (op S)` can be constructed from a compatible family of
morphisms `x : E ⟶ P.obj (op (X i))`.
-/
def IsSheaf.amalgamateOfArrows : E ⟶ P.obj (op S) :=
  (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose

@[reassoc (attr := simp)]
/-
**CategoryTheory.Presheaf.IsSheaf.amalgamateOfArrows_map** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheory.Grothendieck
Topology C} {P : CategoryTheory.Functor Cᵒᵖ A}   (hP : CategoryTheory.Presheaf.I
sSheaf J P) {I : Type u_1} {S : C} {X : I → C} (f : (i : I) → X i ⟶ S)   (hf : C
ategoryTheory.Sieve.ofArrows X f ∈ J S) {E : A} (x : (i : I) → E ⟶ P.obj (Opposi
te.op (X i)))   (hx :     ∀ ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),      
 CategoryTheory.CategoryStruct.comp a (f i) = CategoryTheory.CategoryStruct.comp
 b (f j) →         CategoryTheory.CategoryStruct.comp (x i) (P.map a.op) = Categ
oryTheory.CategoryStruct.comp (x j) (P.map b.op))   (i : I), CategoryTheory.Cate
goryStruct.comp (hP.amalgamateOfArrows f hf x hx) (P.map (f i).op) = x i
参数：hP : CategoryTheory.Presheaf.IsSheaf J P；f : (i : I) → X i ⟶ S；hf : CategoryT
heory.Sieve.ofArrows X f ∈ J S；x : (i : I) → E ⟶ P.obj (Opposite.op (X i))；hx : 
    ∀ ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),       CategoryTheory.Catego
ryStruct.comp a (f i) = CategoryTheory.CategoryStruct.comp b (f j) →         Cat
egoryTheory.CategoryStruct.comp (x i) (P.map a.op) = CategoryTheory.CategoryStru
ct.comp (x j) (P.map b.op)；i : I；hP.amalgamateOfArrows f hf x hx；P.map (f i).op。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A]   {J : CategoryTheor…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma IsSheaf.amalgamateOfArrows_map (i : I) :
    hP.amalgamateOfArrows f hf x hx ≫ P.map (f i).op = x i :=
  (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose_spec.1 i

end

/-
**CategoryTheory.Presheaf.isSheaf_of_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presheaf`。
形式化陈述：isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J
 P'
参数：e : P ≅ P'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.Presieve.isSheaf_iso`：isSheaf_iso {P' : Cᵒᵖ ⥤ Type w} (i 
: P ≅ P') (h : IsSheaf J P) : IsSheaf J P'
-/
theorem isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P' :=
  forall_congr' fun _ =>
    ⟨Presieve.isSheaf_iso J (Functor.isoWhiskerRight e _),
      Presieve.isSheaf_iso J (Functor.isoWhiskerRight e.symm _)⟩

variable (J)
/-
**CategoryTheory.Presheaf.isSheaf_of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：isSheaf_of_isTerminal {X : A} (hX : IsTerminal X) : Presheaf.IsSheaf J ((C
ategoryTheory.Functor.const _).obj X)
参数：hX : IsTerminal X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem isSheaf_of_isTerminal {X : A} (hX : IsTerminal X) :
    Presheaf.IsSheaf J ((CategoryTheory.Functor.const _).obj X) := fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩

end Presheaf

variable {C : Type u₁} [Category.{v₁} C]
variable (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/-- The category of sheaves taking values in `A` on a Grothendieck topology. -/
/-
**CategoryTheory.Sheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：Sheaf
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of sheaves taking values in `A` on a Grothendieck topology.
-/
abbrev Sheaf := ObjectProperty.FullSubcategory (Presheaf.IsSheaf J (A := A))

section

variable {J A}

/-- The underlying presheaf of a sheaf. -/
@[deprecated "Use ObjectProperty.obj" (since := "2026-03-03")]
/-
**CategoryTheory.Sheaf.val** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] → CategoryTheory.Sheaf J A → CategoryTheory.
Functor Cᵒᵖ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying presheaf of a sheaf.
-/
abbrev Sheaf.val (F : Sheaf J A) : Cᵒᵖ ⥤ A := F.obj

@[deprecated "Use ObjectProperty.FullSubcategory.property" (since := "2026-03-03")]
/-
**CategoryTheory.Sheaf.cond** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] (F : CategoryTheory.Sheaf J A), CategoryTheory.Presheaf.IsSheaf J F.
obj
参数：F : CategoryTheory.Sheaf J A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma Sheaf.cond (F : Sheaf J A) : Presheaf.IsSheaf J F.obj := F.property

@[deprecated (since := "2026-03-03")]
alias Sheaf.Hom.mk := ObjectProperty.homMk
/-
**CategoryTheory.Sheaf.hom_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.She
af`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {F G : CategoryTheory.Sheaf J A} {f g : F ⟶ G}, f = g ↔ f.hom = g.ho
m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma Sheaf.hom_ext_iff {F G : Sheaf J A} {f g : F ⟶ G} :
    f = g ↔ f.hom = g.hom := by
  cat_disch
/-
**CategoryTheory.Sheaf.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {F G : CategoryTheory.Sheaf J A} {f g : F ⟶ G}, f.hom = g.hom → f = 
g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sheaf.hom_ext {F G : Sheaf J A} {f g : F ⟶ G} (h : f.hom = g.hom) :
    f = g := by
  cat_disch

end

/-- The inclusion functor of the category of sheaves in the category of presheaves. -/
/-
**CategoryTheory.sheafToPresheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor of the category of sheaves in the category of presheaves.
-/
abbrev sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A := ObjectProperty.ι _

/-- The sections of a sheaf (i.e. evaluation as a presheaf on `C`). -/
/-
**CategoryTheory.sheafSections** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafSections : Cᵒᵖ ⥤ Sheaf J A ⥤ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sections of a sheaf (i.e. evaluation as a presheaf on `C`).
-/
abbrev sheafSections : Cᵒᵖ ⥤ Sheaf J A ⥤ A := (sheafToPresheaf J A).flip

/-- The sheaf sections functor on `X` is given by evaluation of presheaves on `X`. -/
@[simps!]
/-
**CategoryTheory.sheafSectionsNatIsoEvaluation** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：sheafSectionsNatIsoEvaluation {X : C} : (sheafSections J A).obj (op X) ≅ s
heafToPresheaf J A ⋙ (evaluation _ _).obj (op X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf sections functor on `X` is given by evaluation of presheaves on `X`.
-/
def sheafSectionsNatIsoEvaluation {X : C} :
    (sheafSections J A).obj (op X) ≅ sheafToPresheaf J A ⋙ (evaluation _ _).obj (op X) :=
  Iso.refl _

/-- The functor `Sheaf J A ⥤ Cᵒᵖ ⥤ A` is fully faithful. -/
/-
**CategoryTheory.fullyFaithfulSheafToPresheaf** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：fullyFaithfulSheafToPresheaf : (sheafToPresheaf J A).FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Sheaf J A ⥤ Cᵒᵖ ⥤ A` is fully faithful.
-/
abbrev fullyFaithfulSheafToPresheaf : (sheafToPresheaf J A).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

section

variable {J A}

/-- The bijection `(X ⟶ Y) ≃ (X.val ⟶ Y.val)` when `X` and `Y` are sheaves. -/
/-
**CategoryTheory.Sheaf.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] → {X Y : CategoryTheory.Sheaf J A} → (X ⟶ Y)
 ≃ (X.obj ⟶ Y.obj)
参数：X ⟶ Y；X.obj ⟶ Y.obj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X ⟶ Y) ≃ (X.val ⟶ Y.val)` when `X` and `Y` are sheaves.
-/
abbrev Sheaf.homEquiv {X Y : Sheaf J A} : (X ⟶ Y) ≃ (X.obj ⟶ Y.obj) :=
  (fullyFaithfulSheafToPresheaf J A).homEquiv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `Sheaf.homEquiv` as a natural isomorphism. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf : sheafToPreshe
af J A ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A).op ≅ 
yoneda
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sheaf.homEquiv` as a natural isomorphism.
-/
def sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf :
    sheafToPresheaf J A ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A).op ≅
      yoneda :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftYonedaIsoYoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftYonedaCompWhiskeringLeft ≪≫
    uliftYonedaIsoYoneda
/-
**CategoryTheory.sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_
app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : 
Sheaf J A} : (sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf.app X).
app (op Y) = Sheaf.homEquiv.symm.toIso
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : Sheaf J A} :
    (sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf.app X).app (op Y) =
      Sheaf.homEquiv.symm.toIso :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `Sheaf.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf : (sheafToPre
sheaf J A).op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J
 A) ≅ coyoneda
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sheaf.homEquiv` as a natural isomorphism, using coyoneda.
-/
def sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf :
    (sheafToPresheaf J A).op ⋙ coyoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A) ≅
      coyoneda :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftCoyonedaIsoCoyoneda.{max u₁ v₂}.symm _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftCoyonedaCompWhiskeringLeft ≪≫
    uliftCoyonedaIsoCoyoneda
/-
**CategoryTheory.sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_ap
p_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y 
: Sheaf J A} : (sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.app
 (op X)).app Y = Sheaf.homEquiv.symm.toIso
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : Sheaf J A} :
    (sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.app (op X)).app Y =
      Sheaf.homEquiv.symm.toIso :=
  rfl

end

/-- This is stated as a lemma to prevent class search from forming a loop since a sheaf morphism is
monic if and only if it is monic as a presheaf morphism (under suitable assumption). -/
/-
**CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Sheaf.Hom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryT
heory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {F G : CategoryTheory.Sheaf J A} (f : F ⟶ G)   [h : CategoryTheory.M
ono f.hom], CategoryTheory.Mono f
参数：J : CategoryTheory.GrothendieckTopology C；A : Type u₂；f : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
This is stated as a lemma to prevent class search from forming a loop since a sh
eaf morphism is
monic if and only if it is monic as a presheaf morphism (under suitable assumpti
on).
-/
theorem Sheaf.Hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1] : Mono f :=
  (sheafToPresheaf J A).mono_of_mono_map h
/-
**CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Sheaf.Hom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryT
heory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {F G : CategoryTheory.Sheaf J A} (f : F ⟶ G)   [h : CategoryTheory.E
pi f.hom], CategoryTheory.Epi f
参数：J : CategoryTheory.GrothendieckTopology C；A : Type u₂；f : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape`：∀ {C : T
ype u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
instance Sheaf.Hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1] : Epi f :=
  (sheafToPresheaf J A).epi_of_epi_map h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.isSheaf_iff_isSheaf_of_type** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Pr
esieve.IsSheaf J P
参数：P : Cᵒᵖ ⥤ Type w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheaf_iso`：isSheaf_iso {P' : Cᵒᵖ ⥤ Type w} (i 
: P ≅ P') (h : IsSheaf J P) : IsSheaf J P'
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P := by
  constructor
  · intro hP
    refine Presieve.isSheaf_iso J ?_ (hP (PUnit))
    exact Functor.isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine ⟨↾fun x => (hP S hS).amalgamate (fun Z f hf ↦
      (ConcreteCategory.hom (z f hf)) x) ?_, ?_, ?_⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact (ConcreteCategory.congr_hom (hz g₁ g₂ hf₁ hf₂ h)) x
    · intro Z f hf
      apply ConcreteCategory.hom_ext
      intro x
      simp only [Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Functor.comp_map,
        Functor.flip_obj_map, yoneda_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        comp_apply]
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      apply ConcreteCategory.hom_ext
      intro x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      simp [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps]
/-
**CategoryTheory.sheafOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ 
: Sheaf J A) (E : A) : Sheaf J (Type _) where obj
参数：ℱ : Sheaf J A；E : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf of sections guaranteed by the sheaf condition.
-/
def sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A) :
    Sheaf J (Type _) where
  obj := ℱ.obj ⋙ coyoneda.obj (op E)
  property := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact ℱ.property E

variable {J} in
/-
**CategoryTheory.Presheaf.IsSheaf.isSheafFor** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {P : CategoryTheory.Functor Cᵒᵖ (Type w)},   Cat
egoryTheory.Presheaf.IsSheaf J P → ∀ {X : C}, ∀ S ∈ J X, CategoryTheory.Presieve
.IsSheafFor P S.arrows
参数：Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
-/
lemma Presheaf.IsSheaf.isSheafFor {P : Cᵒᵖ ⥤ Type w} (hP : Presheaf.IsSheaf J P)
    {X : C} (S : Sieve X) (hS : S ∈ J X) : Presieve.IsSheafFor P S.arrows := by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  exact hP S hS

variable {A} in
/-
**CategoryTheory.Presheaf.isSheaf_bot** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Presheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} A]   (P : CategoryTheory.Functor Cᵒᵖ 
A), CategoryTheory.Presheaf.IsSheaf ⊥ P
参数：P : CategoryTheory.Functor Cᵒᵖ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheaf_bot`：isSheaf_bot : IsSheaf (⊥ : Grothend
ieckTopology C) P
-/
lemma Presheaf.isSheaf_bot (P : Cᵒᵖ ⥤ A) : IsSheaf ⊥ P := fun _ ↦ Presieve.isSheaf_bot

variable {A J} in
/-
**CategoryTheory.Presheaf.IsSheaf.of_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Presheaf.IsSheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {K : CategoryTheory.GrothendieckTopology C}   {F : CategoryTheory.Fu
nctor Cᵒᵖ A}, J ≤ K → CategoryTheory.Presheaf.IsSheaf K F → CategoryTheory.Presh
eaf.IsSheaf J F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Presheaf.IsSheaf.of_le {K : GrothendieckTopology C} {F : Cᵒᵖ ⥤ A} (hle : J ≤ K)
    (h : Presheaf.IsSheaf K F) :
    Presheaf.IsSheaf J F :=
  fun _ _ _ hS ↦ h _ _ (hle _ hS)

set_option backward.isDefEq.respectTransparency.types false in
/--
The category of sheaves on the bottom (trivial) Grothendieck topology is
equivalent to the category of presheaves.
-/
@[simps]
/-
**CategoryTheory.sheafBotEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafBotEquivalence : Sheaf (⊥ : GrothendieckTopology C) A ≌ Cᵒᵖ ⥤ A where
 functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_bot`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} A]   (P : CategoryTheor…

--- 原说明 ---
The category of sheaves on the bottom (trivial) Grothendieck topology is
equivalent to the category of presheaves.
-/
def sheafBotEquivalence : Sheaf (⊥ : GrothendieckTopology C) A ≌ Cᵒᵖ ⥤ A where
  functor := sheafToPresheaf _ _
  inverse :=
    { obj := fun P => ⟨P, Presheaf.isSheaf_bot P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Sheaf (⊥ : GrothendieckTopology C) (Type w)) :=
  ⟨(sheafBotEquivalence _).inverse.obj ((Functor.const _).obj default)⟩

variable {J} {A}

/-- If the empty sieve is a cover of `X`, then `F(X)` is terminal. -/
/-
**CategoryTheory.Sheaf.isTerminalOfBotCover** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Sheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] →           (F : CategoryTheory.Sheaf J A) →
             (X : C) → ⊥ ∈ J X → CategoryTheory.Limits.IsTerminal (F.obj.obj (Op
posite.op X))
参数：F : CategoryTheory.Sheaf J A；X : C；F.obj.obj (Opposite.op X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the empty sieve is a cover of `X`, then `F(X)` is terminal.
-/
def Sheaf.isTerminalOfBotCover (F : Sheaf J A) (X : C) (H : ⊥ ∈ J X) :
    IsTerminal (F.1.obj (op X)) := by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩

variable (J) in
/-- A terminal object in `A` gives rise to a terminal object in `Sheaf J` -/
@[simps]
/-
**CategoryTheory.Sheaf.terminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (J : C
ategoryTheory.GrothendieckTopology C) →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] →           {X : A} → CategoryTheory.Limits.
IsTerminal X → CategoryTheory.Sheaf J A
参数：J : CategoryTheory.GrothendieckTopology C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_isTerminal`：isSheaf_of_isTerminal {X 
: A} (hX : IsTerminal X) : Presheaf.IsSheaf J ((CategoryTheory.Functor.const _).
obj X)

--- 原说明 ---
A terminal object in `A` gives rise to a terminal object in `Sheaf J`
-/
def Sheaf.terminal {X : A} (hX : IsTerminal X) : Sheaf J A where
  obj := (CategoryTheory.Functor.const _).obj X
  property := Presheaf.isSheaf_of_isTerminal J hX

variable (J) in
/-- The constant sheaf of a terminal object is indeed terminal -/
/-
**CategoryTheory.Sheaf.isTerminalTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (J : C
ategoryTheory.GrothendieckTopology C) →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] →           {X : A} →             (hX : Cate
goryTheory.Limits.IsTerminal X) →               CategoryTheory.Limits.IsTerminal
 (CategoryTheory.Sheaf.terminal J hX)
参数：J : CategoryTheory.GrothendieckTopology C；hX : CategoryTheory.Limits.IsTermin
al X；CategoryTheory.Sheaf.terminal J hX。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant sheaf of a terminal object is indeed terminal
-/
def Sheaf.isTerminalTerminal {X : A} (hX : IsTerminal X) : IsTerminal (Sheaf.terminal J hX) :=
  .ofUniqueHom (⟨(Functor.isTerminalConst _ hX).from ·.obj⟩)
    (by intros; ext; simpa using! hX.hom_ext _ _)

@[simp]
/-
**CategoryTheory.Sheaf.isTerminalTerminal_from_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] {X : A} (hX : CategoryTheory.Limits.IsTerminal X)   (G : CategoryThe
ory.Sheaf J A),   ((CategoryTheory.Sheaf.isTerminalTerminal J hX).from G).hom = 
    (CategoryTheory.Functor.isTerminalConst Cᵒᵖ hX).from G.obj
参数：hX : CategoryTheory.Limits.IsTerminal X；G : CategoryTheory.Sheaf J A；(Categor
yTheory.Sheaf.isTerminalTerminal J hX).from G；CategoryTheory.Functor.isTerminalC
onst Cᵒᵖ hX。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sheaf.isTerminalTerminal_from_hom {X : A} (hX : IsTerminal X) (G : Sheaf J A) :
    ((Sheaf.isTerminalTerminal J hX).from G).hom = (Functor.isTerminalConst _ hX).from G.obj := rfl

/-- If the topology is discrete, any sheaf is terminal. -/
/-
**CategoryTheory.Sheaf.isTerminalOfEqTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Sheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {A : Type u₂} →         [inst_1 : 
CategoryTheory.Category.{v₂, u₂} A] →           J = ⊤ → (F : CategoryTheory.Shea
f J A) → CategoryTheory.Limits.IsTerminal F
参数：F : CategoryTheory.Sheaf J A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the topology is discrete, any sheaf is terminal.
-/
noncomputable def Sheaf.isTerminalOfEqTop (H : J = ⊤) (F : Sheaf J A) :
    IsTerminal F := by
  refine IsTerminal.isTerminalOfObj (sheafToPresheaf _ _) _ ?_
  refine Functor.isTerminal fun X ↦ Sheaf.isTerminalOfBotCover _ _ ?_
  simp [H]

@[simp]
/-
**CategoryTheory.Sheaf.Hom.add_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.She
af.Hom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} {A : Type u₂}   [inst_1 : CategoryTheory.Category.
{v₂, u₂} A] [inst_2 : CategoryTheory.Preadditive A] {P Q : CategoryTheory.Sheaf 
J A}   (f g : P ⟶ Q) (U : Cᵒᵖ), (f + g).hom.app U = f.hom.app U + g.hom.app U
参数：f g : P ⟶ Q；U : Cᵒᵖ；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sheaf.Hom.add_app [Preadditive A] {P Q : Sheaf J A} (f g : P ⟶ Q) (U : Cᵒᵖ) :
    (f + g).1.app U = f.1.app U + g.1.app U :=
  rfl

end CategoryTheory

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

-- Under here is the equalizer story, which is equivalent if A has products (and doesn't
-- make sense otherwise). It's described in https://stacks.math.columbia.edu/tag/00VL,
-- between 00VQ and 00VR.
variable {C : Type u₁} [Category.{v₁} C]

-- `A` is a general category; `A'` is a variant where the morphisms live in a large enough
-- universe to guarantee that we can take limits in A of things coming from C.
-- I would have liked to use something like `UnivLE.{max v₁ u₁, v₂}` as a hypothesis on
-- `A`'s morphism universe rather than introducing `A'` but I can't get it to work.
-- So, for now, results which need max v₁ u₁ ≤ v₂ are just stated for `A'` and `P' : Cᵒᵖ ⥤ A'`
-- instead.
variable {A : Type u₂} [Category.{v₂} A]
variable {A' : Type u₂} [Category.{max v₁ u₁} A']
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (P : Cᵒᵖ ⥤ A) (P' : Cᵒᵖ ⥤ A')

section MultiequalizerConditions

set_option backward.isDefEq.respectTransparency.types false in
/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
/-
**CategoryTheory.Presheaf.isLimitOfIsSheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Presheaf`。
形式化陈述：isLimitOfIsSheaf {X : C} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.m
ultifork P) where lift
参数：S : J.Cover X；hP : IsSheaf J P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `P` is a sheaf and `S` is a cover, the associated multifork is a limit.
-/
def isLimitOfIsSheaf {X : C} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.multifork P) where
  lift := fun E : Multifork _ => hP.amalgamate S (fun _ => E.ι _)
    (fun _ _ r => E.condition ⟨r⟩)
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate_map

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Presheaf.isSheaf_iff_multifork** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：isSheaf_iff_multifork : IsSheaf J P ↔ forall (X : C) (S : J.Cover X), None
mpty (IsLimit (S.multifork P))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation.w`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.Grothen
dieckTopology C}   {S : J.Cover X} {I₁ I₂ : S.Ar…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem isSheaf_iff_multifork :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P)) := by
  refine ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, ?_⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf)
    (fun I => hx _ _ _ _ I.r.w)
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply he

variable {J P} in
/-- If `F : Cᵒᵖ ⥤ A` is a sheaf for a Grothendieck topology `J` on `C`,
and `S` is a cover of `X : C`, then the multifork `S.multifork F` is limit. -/
/-
**CategoryTheory.Presheaf.IsSheaf.isLimitMultifork** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Presheaf.IsSheaf`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {A : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} A] →         {J : Cat
egoryTheory.GrothendieckTopology C} →           {P : CategoryTheory.Functor Cᵒᵖ 
A} →             CategoryTheory.Presheaf.IsSheaf J P →               {X : C} → (
S : J.Cover X) → CategoryTheory.Limits.IsLimit (S.multifork P)
参数：S : J.Cover X；S.multifork P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ A` is a sheaf for a Grothendieck topology `J` on `C`,
and `S` is a cover of `X : C`, then the multifork `S.multifork F` is limit.
-/
def IsSheaf.isLimitMultifork
    (hP : Presheaf.IsSheaf J P) {X : C} (S : J.Cover X) : IsLimit (S.multifork P) := by
  rw [Presheaf.isSheaf_iff_multifork] at hP
  exact (hP X S).some

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.isSheaf_iff_multiequalizer** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_multiequalizer [forall (X : C) (S : J.Cover X), HasMultiequali
zer (S.index P)] : IsSheaf J P ↔ forall (X : C) (S : J.Cover X), IsIso (S.toMult
iequalizer P)
参数：X : C；S : J.Cover X；S.index P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_multifork`：isSheaf_iff_multifork : I
sSheaf J P ↔ forall (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P))
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Multifork.ofι_π_app`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   (I : 
CategoryTheory.Limits.Multicosp…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.index_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTo
pology C}   {D : Type u₁} [inst_1 : Categ…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSheaf_iff_multiequalizer [∀ (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), IsIso (S.toMultiequalizer P) := by
  rw [isSheaf_iff_multifork]
  refine forall₂_congr fun X S => ⟨?_, ?_⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ?_ ?_)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      simp

end MultiequalizerConditions

section

variable [HasProducts.{max u₁ v₁} A]
variable [HasProducts.{max u₁ v₁} A']

/-- The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork
diagram of the Stacks entry. -/
@[stacks 00VM "The middle object of the fork diagram there."]
/-
**CategoryTheory.Presheaf.firstObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pre
sheaf`。
形式化陈述：firstObj : A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The middle object of the fork diagram given in Equation (3) of [MM92], as well a
s the fork
diagram of the Stacks entry.
-/
def firstObj : A :=
  ∏ᶜ fun f : Σ V, { f : V ⟶ U // R f } => P.obj (op f.1)

/-- The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork
diagram of the Stacks entry. -/
@[stacks 00VM "The left morphism the fork diagram there."]
/-
**CategoryTheory.Presheaf.forkMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pres
heaf`。
形式化陈述：forkMap : P.obj (op U) ⟶ firstObj R P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left morphism of the fork diagram given in Equation (3) of [MM92], as well a
s the fork
diagram of the Stacks entry.
-/
def forkMap : P.obj (op U) ⟶ firstObj R P :=
  Pi.lift fun f => P.map f.2.1.op

variable [HasPullbacks C]

/-- The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[stacks 00VM "The rightmost object of the fork diagram there."]
/-
**CategoryTheory.Presheaf.secondObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
esheaf`。
形式化陈述：secondObj : A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatibl
e.
-/
def secondObj : A :=
  ∏ᶜ fun fg : (Σ V, { f : V ⟶ U // R f }) × Σ W, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₀*` there."]
/-
**CategoryTheory.Presheaf.firstMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pre
sheaf`。
形式化陈述：firstMap : firstObj R P ⟶ secondObj R P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `pr₀*` of the Stacks entry.
-/
def firstMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/-- The map `pr₁*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₁*` there."]
/-
**CategoryTheory.Presheaf.secondMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
esheaf`。
形式化陈述：secondMap : firstObj R P ⟶ secondObj R P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `pr₁*` of the Stacks entry.
-/
def secondMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P := by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

/-- An alternative definition of the sheaf condition in terms of equalizers. This is shown to be
equivalent in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
-/
/-
**CategoryTheory.Presheaf.IsSheaf'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pre
sheaf`。
形式化陈述：IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.w`：w : forkMap R P ≫ firstMap R P = forkMap R P 
≫ secondMap R P

--- 原说明 ---
An alternative definition of the sheaf condition in terms of equalizers. This is
 shown to be
equivalent in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
-/
def IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ (U : C) (R : Presieve U) (_ : generate R ∈ J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Again I wonder whether `UnivLE` can somehow be used to allow `s` to take
-- values in a more general universe.
/-- (Implementation). An auxiliary lemma to convert between sheaf conditions. -/
/-
**CategoryTheory.Presheaf.isSheafForIsSheafFor'** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type (max v₁ u₁)) [forall J, 
PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) : Is
Limit (s.mapCone (Fork.ofι _ (w R P))) ≃ IsLimit (Fork.ofι _ (Equalizer.Presieve
.w (P ⋙ s) R))
参数：P : Cᵒᵖ ⥤ A；s : A ⥤ Type (max v₁ u₁)；Discrete.{max v₁ u₁} J；U : C；R : Presiev
e U。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Presheaf.w`：w : forkMap R P ≫ firstMap R P = forkMap R P 
≫ secondMap R P
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
(Implementation). An auxiliary lemma to convert between sheaf conditions.
-/
def isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type (max v₁ u₁))
    [∀ J, PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) :
    IsLimit (s.mapCone (Fork.ofι _ (w R P))) ≃
      IsLimit (Fork.ofι _ (Equalizer.Presieve.w (P ⋙ s) R)) := by
  let e : parallelPair (s.map (firstMap R P)) (s.map (secondMap R P)) ≅
    parallelPair (Equalizer.Presieve.firstMap (P ⋙ s) R)
      (Equalizer.Presieve.secondMap (P ⋙ s) R) := by
    refine parallelPair.ext (PreservesProduct.iso s _) ((PreservesProduct.iso s _))
      (limit.hom_ext (fun j => ?_)) (limit.hom_ext (fun j => ?_))
    · dsimp [Equalizer.Presieve.firstMap, firstMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
    · dsimp [Equalizer.Presieve.secondMap, secondMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
  refine Equiv.trans (isLimitMapConeForkEquiv _ _) ?_
  refine (IsLimit.postcomposeHomEquiv e _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) ?_))
  dsimp [Equalizer.forkMap, forkMap, e, Fork.ι]
  simp only [id_comp, map_lift_piComparison]

-- Remark : this lemma uses `A'` not `A`; `A'` is `A` but with a universe
-- restriction. Can it be generalised?
/-- The equalizer definition of a sheaf given by `isSheaf'` is equivalent to `isSheaf`. -/
/-
**CategoryTheory.Presheaf.isSheaf_iff_isSheaf'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Presheaf`。
形式化陈述：isSheaf_iff_isSheaf' : IsSheaf J P' ↔ IsSheaf' J P'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.w`：w : forkMap R P ≫ firstMap R P = forkMap R P 
≫ secondMap R P
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `CategoryTheory.Equalizer.Presieve.w`：w : forkMap P R ≫ firstMap P R = fo
rkMap P R ≫ secondMap P R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equalizer.Presieve.sheaf_condition`：sheaf_condition : R.I
sSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R)))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.coyonedaPreservesLimitsOfShape`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (J : Type w) [inst_1 : CategoryTheory.Category.{
t, w} J]   (X : Cᵒᵖ), CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S

--- 原说明 ---
The equalizer definition of a sheaf given by `isSheaf'` is equivalent to `isShea
f`.
-/
theorem isSheaf_iff_isSheaf' : IsSheaf J P' ↔ IsSheaf' J P' := by
  constructor
  · intro h U R hR
    refine ⟨?_⟩
    apply coyonedaJointlyReflectsLimits
    intro X
    have q : Presieve.IsSheafFor (P' ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← Presieve.isSheafFor_iff_generate] at q
    rw [Equalizer.Presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (isSheafForIsSheafFor' _ _ _ _).symm q
  · intro h U X S hS
    rw [Equalizer.Presieve.sheaf_condition]
    refine ⟨?_⟩
    refine isSheafForIsSheafFor' _ _ _ _ ?_
    letI := preservesSmallestLimits_of_preservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa

end

section Concrete

/-
**CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presheaf`。
形式化陈述：isSheaf_of_isSheaf_comp (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} 
s] (h : IsSheaf J (P ⋙ s)) : IsSheaf J P
参数：s : A ⥤ B；h : IsSheaf J (P ⋙ s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit`：isSheaf_iff_isLimit : IsShe
af J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone 
S.arrows.cocone.op))
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
-/
theorem isSheaf_of_isSheaf_comp (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J (P ⋙ s)) : IsSheaf J P := by
  rw [isSheaf_iff_isLimit] at h ⊢
  exact fun X S hS ↦ (h S hS).map fun t ↦ isLimitOfReflects s t
/-
**CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Presheaf`。
形式化陈述：isSheaf_comp_of_isSheaf (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁}
 s] (h : IsSheaf J P) : IsSheaf J (P ⋙ s)
参数：s : A ⥤ B；h : IsSheaf J P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit`：isSheaf_iff_isLimit : IsShe
af J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone 
S.arrows.cocone.op))
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
theorem isSheaf_comp_of_isSheaf (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J P) : IsSheaf J (P ⋙ s) := by
  rw [isSheaf_iff_isLimit] at h ⊢
  apply fun X S hS ↦ (h S hS).map fun t ↦ isLimitOfPreserves s t
/-
**CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_isSheaf_comp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A] [
PreservesLimitsOfSize.{v₁, max v₁ u₁} s] [s.ReflectsIsomorphisms] : IsSheaf J P 
↔ IsSheaf J (P ⋙ s)
参数：s : A ⥤ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms`：reflectsLi
mits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] [HasLimitsOfSi
ze.{w', w} C] [PreservesLimitsOfSize.{w', w} G] : …
· 使用定理 `CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf`：isSheaf_comp_of_isSheaf
 (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] (h : IsSheaf J P) : IsShe
af J (P ⋙ s)
· 使用定理 `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`：isSheaf_of_isSheaf_comp
 (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s] (h : IsSheaf J (P ⋙ s)) : 
IsSheaf J P
-/
theorem isSheaf_iff_isSheaf_comp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A]
    [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] [s.ReflectsIsomorphisms] :
    IsSheaf J P ↔ IsSheaf J (P ⋙ s) := by
  let : ReflectsLimitsOfSize s := reflectsLimits_of_reflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩

/--
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` preserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, e.g. groups, abelian groups and rings, but not
for the category of topological spaces, topological rings, etc. since reflecting isomorphisms does
not hold.
-/
/-
**CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：isSheaf_iff_isSheaf_forget (s : A' ⥤ Type (max v₁ u₁)) [HasLimits A'] [Pre
servesLimits s] [s.ReflectsIsomorphisms] : IsSheaf J P' ↔ IsSheaf J (P' ⋙ s)
参数：s : A' ⥤ Type (max v₁ u₁)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfSizeShrink`：hasLimitsOfSizeShrink [HasL
imitsOfSize.{max v₁ v₂, max u₁ u₂} C] : HasLimitsOfSize.{v₁, u₁} C
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfSize_shrink`：preservesLimitsOfSiz
e_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] : Preserve
sLimitsOfSize.{w, w'} F
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp`：isSheaf_iff_isSheaf_co
mp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A] [PreservesLimitsOfSize.{v₁, m
ax v₁ u₁} s] [s.ReflectsIsomorphisms] …

--- 原说明 ---
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` pr
eserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` 
is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, e.g. groups, abelian groups 
and rings, but not
for the category of topological spaces, topological rings, etc. since reflecting
 isomorphisms does
not hold.
-/
theorem isSheaf_iff_isSheaf_forget (s : A' ⥤ Type (max v₁ u₁)) [HasLimits A'] [PreservesLimits s]
    [s.ReflectsIsomorphisms] : IsSheaf J P' ↔ IsSheaf J (P' ⋙ s) := by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSize_shrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp

end Concrete

end Presheaf

end CategoryTheory

