/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## Main definitions

- `CategoryTheory.MorphismProperty.ind`: `f` satisfies `ind P` if `f` is a filtered colimit of
  morphisms in `P`.

## Main results:

- `CategoryTheory.MorphismProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `pro P`.
- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

@[expose] public section

universe w v u

namespace CategoryTheory.MorphismProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

/--
Let `P` be a property of morphisms. `P.ind` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : X ⟶ Yᵢ` and `sᵢ : Yᵢ ⟶ Y` indexed by `J`
such that
- `J` is filtered
- `Y ≅ colim Yᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = tᵢ ≫ sᵢ` for all `i`.

See `CategoryTheory.MorphismProperty.ind_iff_ind_under_mk` for an equivalent characterization
in terms of `Y` as an object of `Under X`.
-/
/-
**CategoryTheory.MorphismProperty.ind** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
MorphismProperty`。
形式化陈述：ind (P : MorphismProperty C) : MorphismProperty C
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P` be a property of morphisms. `P.ind` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : X ⟶ Yᵢ` and `sᵢ : Yᵢ ⟶ Y` indexed
 by `J`
such that
- `J` is filtered
- `Y ≅ colim Yᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = tᵢ ≫ sᵢ` for all `i`.

See `CategoryTheory.MorphismProperty.ind_iff_ind_under_mk` for an equivalent cha
racterization
in terms of `Y` as an object of `Under X`.
-/
def ind (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ C) (t : (Functor.const J).obj X ⟶ D) (s : D ⟶ (Functor.const J).obj Y)
    (_ : IsColimit (Cocone.mk _ s)), ∀ j, P (t.app j) ∧ t.app j ≫ s.app j = f
/-
**CategoryTheory.MorphismProperty.exists_hom_of_isFinitelyPresentable** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：exists_hom_of_isFinitelyPresentable {J : Type w} [SmallCategory J] [IsFilt
ered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X A : C} {p : X ⟶ A} (hp 
: isFinitelyPresentable.{w} C p) (s : (Functor.const J).obj X ⟶ D) (f : A ⟶ c.pt
) (h : forall (j : J), s.app j ≫ c.ι.app j = p ≫ f) : exists (j : J) (q : A ⟶ D.
obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f
参数：hc : IsColimit c；hp : isFinitelyPresentable.{w} C p；s : (Functor.const J).obj
 X ⟶ D；f : A ⟶ c.pt；h : forall (j : J), s.app j ≫ c.ι.app j = p ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit_under`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Cate
goryTheory.SmallCategory J]   [CategoryTheory.IsFiltered…
-/
lemma exists_hom_of_isFinitelyPresentable {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    {c : Cocone D} (hc : IsColimit c) {X A : C} {p : X ⟶ A} (hp : isFinitelyPresentable.{w} C p)
    (s : (Functor.const J).obj X ⟶ D) (f : A ⟶ c.pt) (h : ∀ (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    ∃ (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f :=
  hp.exists_hom_of_isColimit_under hc _ s _ h

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.le_ind** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.MorphismProperty`。
形式化陈述：le_ind : P <= ind.{w} P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isFiltered_of_directed_le_nonempty`：∀ (α : Type u) [inst 
: Preorder α] [IsDirectedOrder α] [Nonempty α], CategoryTheory.IsFiltered α
· 使用定理 `OrderTop.instIsDirectedOrder`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.isConnected_of_nonempty_and_subsingleton`：∀ {J : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} J] [Nonempty J] [Subsingleton J], Cate
goryTheory.IsConnected J
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma le_ind : P ≤ ind.{w} P := by
  intro X Y f hf
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const PUnit).obj Y, ?_, 𝟙 _, ?_, ?_⟩
  · exact { app _ := f }
  · exact isColimitConstCocone _ _
  · simpa

variable {P}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.ind_iff_ind_underMk** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：ind_iff_ind_underMk {X Y : C} (f : X ⟶ Y) : ind.{w} P f ↔ ObjectProperty.i
nd.{w} P.underObj (CategoryTheory.Under.mk f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instPreservesFilteredColimitsOfSizeUnderForget`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C},   Category
Theory.Limits.PreservesFilteredColimitsOfSize.{u_2, u_3, v…
-/
lemma ind_iff_ind_underMk {X Y : C} (f : X ⟶ Y) :
    ind.{w} P f ↔ ObjectProperty.ind.{w} P.underObj (CategoryTheory.Under.mk f) := by
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, pres, hpres⟩ ↦ ?_⟩
  · refine ⟨J, ‹_›, ‹_›, ⟨Under.lift D t, ?_, ?_⟩, ?_⟩
    · exact { app j := CategoryTheory.Under.homMk (s.app j) (by simp [hst]) }
    · have : Nonempty J := IsFiltered.nonempty
      exact Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs
    · simp [underObj, hst]
  · refine ⟨J, ‹_›, ‹_›, pres.diag ⋙ CategoryTheory.Under.forget _, ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
    · exact { app j := (pres.diag.obj j).hom }
    · exact Functor.whiskerRight pres.ι (CategoryTheory.Under.forget X)
    · exact isColimitOfPreserves (CategoryTheory.Under.forget _) pres.isColimit
    · exact hpres j
    · simp
/-
**CategoryTheory.MorphismProperty.underObj_ind_eq_ind_underObj** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：underObj_ind_eq_ind_underObj (X : C) : underObj (ind.{w} P) (X
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma underObj_ind_eq_ind_underObj (X : C) :
    underObj (ind.{w} P) (X := X) = ObjectProperty.ind.{w} P.underObj := by
  ext f
  simp [underObj, show f = CategoryTheory.Under.mk f.hom from rfl, ind_iff_ind_underMk]

variable (Q : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.RespectsLeft Q] : P.ind.RespectsLeft Q where
  precomp {X Y Z} i hi f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j ↦ ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.RespectsIso] : P.ind.RespectsIso where
  postcomp {X Y Z} i (hi : IsIso i) f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j ↦ ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocone.ext (asIso i))) hs
    · simp [reassoc_of% (hst j).2]
/-
**CategoryTheory.MorphismProperty.ind_underObj_pushout** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：ind_underObj_pushout {X Y : C} (g : X ⟶ Y) [HasPushouts C] [P.IsStableUnde
rCobaseChange] {f : Under X} (hf : ObjectProperty.ind.{w} P.underObj f) : Object
Property.ind.{w} P.underObj ((Under.pushout g).obj f)
参数：g : X ⟶ Y；hf : ObjectProperty.ind.{w} P.underObj f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.MorphismProperty.pushout_inr`：pushout_inr {A B A' : C} (f
 : A ⟶ A') (g : A ⟶ B) [HasPushout f g] [P.IsStableUnderCobaseChangeAlong g] (H 
: P f) : P (pushout.inr f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAlongOfIsSt
ableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] {X Y : C
} (…
-/
lemma ind_underObj_pushout {X Y : C} (g : X ⟶ Y) [HasPushouts C] [P.IsStableUnderCobaseChange]
    {f : Under X} (hf : ObjectProperty.ind.{w} P.underObj f) :
    ObjectProperty.ind.{w} P.underObj ((Under.pushout g).obj f) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  use J, inferInstance, inferInstance, pres.map (Under.pushout g)
  intro i
  exact P.pushout_inr _ _ (hpres i)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderCobaseChange] [HasPushouts C] : P.ind.IsStableUnderCobaseChange := by
  refine .mk' fun A B A' f g _ hf ↦ ?_
  rw [ind_iff_ind_underMk] at hf ⊢
  exact ind_underObj_pushout g hf
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] : (ind.{w} P).ContainsIdentities where
  id_mem X := le_ind _ _ (P.id_mem X)

/-- `ind` is idempotent if `P` implies finitely presentable. -/
/-
**CategoryTheory.MorphismProperty.ind_ind** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：ind_ind (hp : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C] : ind
.{w} (ind.{w} P) = ind.{w} P
参数：hp : P <= isFinitelyPresentable.{w} C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.underObj_ind_eq_ind_underObj`：underObj_i
nd_eq_ind_underObj (X : C) : underObj (ind.{w} P) (X
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.ind_ind`：ind_ind (h : P <= isFinitelyPrese
ntable.{w} C) [LocallySmall.{w} C] : ind.{w} (ind.{w} P) = ind.{w} P
· 使用定理 `CategoryTheory.Under.locallySmall`：∀ {T : Type u₃} [inst : CategoryTheor
y.Category.{v₃, u₃} T] (X : T) [CategoryTheory.LocallySmall.{w, v₃, u₃} T],   Ca
tegoryTheory.LocallySma…
· 使用引理 `CategoryTheory.MorphismProperty.le_ind`：le_ind : P <= ind.{w} P

--- 原说明 ---
`ind` is idempotent if `P` implies finitely presentable.
-/
lemma ind_ind (hp : P ≤ isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X Y f hf ↦ ?_) P.ind.le_ind
  have : P.underObj ≤ ObjectProperty.isFinitelyPresentable.{w} (Under X) := fun f hf ↦ hp _ hf
  simpa [ind_iff_ind_underMk, underObj_ind_eq_ind_underObj,
    ObjectProperty.ind_ind.{w} this] using hf

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.ind_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：ind_iff_exists (H : P <= isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y
) [IsFinitelyAccessibleCategory.{w} (Under X)] : ind.{w} P f ↔ forall {Z : C} (p
 : X ⟶ Z) (g : Z ⟶ Y), isFinitelyPresentable.{w} _ p -> p ≫ g = f -> exists (W :
 C) (u : Z ⟶ W) (v : W ⟶ Y), u ≫ v = g ∧ P (p ≫ u)
参数：H : P <= isFinitelyPresentable.{w} C；f : X ⟶ Y；Under X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ind_iff_ind_underMk`：ind_iff_ind_underMk
 {X Y : C} (f : X ⟶ Y) : ind.{w} P f ↔ ObjectProperty.ind.{w} P.underObj (Catego
ryTheory.Under.mk f)
· 使用引理 `CategoryTheory.ObjectProperty.ind_iff_exists`：ind_iff_exists (H : P <= i
sFinitelyPresentable.{w} C) [IsFinitelyAccessibleCategory.{w} C] {X : C} : ind.{
w} P X ↔ forall {Z : C} (g : Z ⟶ X…
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Under.homMk_right`：∀ {T : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X}   (f : U.right ⟶ V.
right)   (w : autoPara…
-/
lemma ind_iff_exists (H : P ≤ isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y)
    [IsFinitelyAccessibleCategory.{w} (Under X)] :
    ind.{w} P f ↔ ∀ {Z : C} (p : X ⟶ Z) (g : Z ⟶ Y),
      isFinitelyPresentable.{w} _ p → p ≫ g = f →
      ∃ (W : C) (u : Z ⟶ W) (v : W ⟶ Y), u ≫ v = g ∧ P (p ≫ u) := by
  rw [ind_iff_ind_underMk, ObjectProperty.ind_iff_exists]
  · refine ⟨fun H Z p g hp hpg ↦ ?_, fun H Z g hZ ↦ ?_⟩
    · have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
      obtain ⟨W, u, v, huv, hW⟩ := H (CategoryTheory.Under.homMk (U := CategoryTheory.Under.mk p)
        (V := CategoryTheory.Under.mk f) g hpg)
      use W.right, u.right, v.right, congr($(huv).right)
      rwa [show p ≫ u.right = W.hom from CategoryTheory.Under.w u]
    · obtain ⟨W, u, v, huv, hW⟩ := H Z.hom g.right hZ (CategoryTheory.Under.w g)
      exact ⟨CategoryTheory.Under.mk (Z.hom ≫ u), CategoryTheory.Under.homMk u,
          CategoryTheory.Under.homMk v, by ext; simpa, hW⟩
  · intro Y hY
    exact H _ hY

/--
A property of morphisms `P` is said to pre-ind-spread if `P`-morphisms out of filtered colimits
descend to a finite level. More precisely, let `Dᵢ` be a filtered family of objects.
Then:

- If `f : colim Dᵢ ⟶ T` satisfies `P`, there exists an index `j` and a pushout square
  ```
    Dⱼ ----f'---> T'
    |             |
    |             |
    v             v
  colim Dᵢ --f--> T
  ```
  such that `f'` satisfies `P`.
-/
/-
**CategoryTheory.MorphismProperty.PreIndSpreads** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：PreIndSpreads (P : MorphismProperty C) : Prop where exists_isPushout {J : 
Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (_ : IsColim
it c) {T : C} (f : c.pt ⟶ T) : P f -> exists (j : J) (T' : C) (f' : D.obj j ⟶ T'
) (g : T' ⟶ T), IsPushout (c.ι.app j) f' f g ∧ P f'  alias exists_isPushout_of_i
sFiltered
参数：P : MorphismProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of morphisms `P` is said to pre-ind-spread if `P`-morphisms out of fi
ltered colimits
descend to a finite level. More precisely, let `Dᵢ` be a filtered family of obje
cts.
Then:

- If `f : colim Dᵢ ⟶ T` satisfies `P`, there exists an index `j` and a pushout s
quare
  ```
    Dⱼ ----f'---> T'
    |             |
    |             |
    v             v
  colim Dᵢ --f--> T
  ```
  such that `f'` satisfies `P`.
-/
class PreIndSpreads (P : MorphismProperty C) : Prop where
  exists_isPushout {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    {c : Cocone D} (_ : IsColimit c) {T : C} (f : c.pt ⟶ T) :
    P f →
    ∃ (j : J) (T' : C) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ P f'

alias exists_isPushout_of_isFiltered := PreIndSpreads.exists_isPushout

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is stable under composition if `P` is. -/
@[stacks 0BSI "The stacks project lemma is for the special case of ind-étale ring homomorphisms."]
/-
**CategoryTheory.MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderComposit
ion`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [∀ (X : C), CategoryTheory.IsFinitelyAccessibleCategory
 (CategoryTheory.Under X)]   [CategoryTheory.Limits.HasPushouts C] [P.IsStableUn
derComposition] [P.IsStableUnderCobaseChange] [P.PreIndSpreads],   P ≤ CategoryT
heory.MorphismProperty.isFinitelyPresentable C → P.ind.IsStableUnderComposition
参数：X : C；CategoryTheory.Under X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ind_iff_exists`：ind_iff_exists (H : P <=
 isFinitelyPresentable.{w} C) {X Y : C} (f : X ⟶ Y) [IsFinitelyAccessibleCategor
y.{w} (Under X)] : ind.{w} P f ↔ for…
· 使用定理 `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit_under`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Cate
goryTheory.SmallCategory J]   [CategoryTheory.IsFiltered…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.MorphismProperty.exists_isPushout_of_isFiltered`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPro
perty C}   [self : P.PreIndSpreads] {J : Type w} [in…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Under.final_forget`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   (Category
Theory.Under.forget c).…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instPreservesFilteredColimitsOfSizeUnderForget`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C},   Category
Theory.Limits.PreservesFilteredColimitsOfSize.{u_2, u_3, v…
· 使用定理 `CategoryTheory.IsFiltered.under`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [CategoryTheory.IsFilteredOrEmpty C] (c : C),   CategoryThe
ory.IsFiltered (Categ…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is stable under composition if `P` is.
-/
lemma IsStableUnderComposition.ind_of_preIndSpreads
    [∀ X : C, (IsFinitelyAccessibleCategory.{w} (Under X))] [HasPushouts C]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] (H : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    rw [ind_iff_exists H]
    intro T p u hp hpu
    obtain ⟨J₁, _, _, D₁, s₁, t₁, ht₁, h₁⟩ := hf
    obtain ⟨J₂, _, _, D₂, s₂, t₂, ht₂, h₂⟩ := hg
    have : IsFinitelyPresentable (CategoryTheory.Under.mk p) := hp
    obtain ⟨j₂, q, hcomp, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
        ht₂ p ((Functor.const _).map f ≫ s₂) u <| by simp [h₂, hpu]
    obtain ⟨j₁, W, f', g', h, hf'⟩ :=
      P.exists_isPushout_of_isFiltered ht₁ (s₂.app j₂) (h₂ j₂).left
    let D' : Under j₁ ⥤ C :=
      (Under.post D₁ ⋙ Under.pushout f') ⋙ CategoryTheory.Under.forget _
    let c' : Cocone D' :=
      (Under.pushout f' ⋙ CategoryTheory.Under.forget _).mapCocone
        ((Cocone.mk _ t₁).underPost j₁) |>.extend h.isoPushout.inv
    let hc' : IsColimit c' :=
      IsColimit.extendIso _ <| isColimitOfPreserves _ (ht₁.underPost j₁)
    let s' : (Functor.const (Under j₁)).obj X ⟶ D' :=
      { app k := s₁.app k.right ≫ pushout.inl _ _
        naturality k l a := by
          have h2 := s₁.naturality a.right
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
          simp [h2, D'] }
    obtain ⟨j₃, v, hcomp', hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under
        hc' p s' q <| fun k ↦ by
      simp [c', s', hcomp, reassoc_of% (h₁ k.right).right]
    refine ⟨D'.obj j₃, v, c'.ι.app j₃ ≫ t₂.app j₂, ?_, ?_⟩
    · rwa [reassoc_of% hq]
    · rw [hcomp']
      exact P.comp_mem _ _ (h₁ _).left (P.pushout_inl _ _ hf')

/-- If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is multiplicative if `P` is. -/
/-
**CategoryTheory.MorphismProperty.IsMultiplicative.ind_of_preIndSpreads** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsMultiplicative`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.MorphismProperty C}   [∀ (X : C), CategoryTheory.IsFinitelyAccessibleCategory
 (CategoryTheory.Under X)]   [CategoryTheory.Limits.HasPushouts C] [P.IsMultipli
cative] [P.IsStableUnderCobaseChange] [P.PreIndSpreads],   P ≤ CategoryTheory.Mo
rphismProperty.isFinitelyPresentable C → P.ind.IsMultiplicative
参数：X : C；CategoryTheory.Under X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.ind_of_preIndSp
reads`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryThe
ory.MorphismProperty C}   [∀ (X : C), CategoryTheory.IsFinitelyAcce…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.instContainsIdentitiesInd`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProperty
 C} [P.ContainsIdentities],   P.ind.ContainsIde…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…

--- 原说明 ---
If `P` ind-spreads and all under categories are finitely accessible, `ind P`
is multiplicative if `P` is.
-/
lemma IsMultiplicative.ind_of_preIndSpreads
    [∀ X : C, (IsFinitelyAccessibleCategory.{w} (Under X))] [HasPushouts C]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange]
    [PreIndSpreads.{w} P] (H : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsMultiplicative where
  __ := IsStableUnderComposition.ind_of_preIndSpreads H

end CategoryTheory.MorphismProperty

