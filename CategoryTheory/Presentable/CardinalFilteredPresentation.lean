/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Presentable.Retracts
public import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Presentable generators

Let `C` be a category, a regular cardinal `κ` and `P : ObjectProperty C`.
We define a predicate `P.IsCardinalFilteredGenerator κ` saying that
`P` consists of `κ`-presentable objects and that any object in `C`
is a `κ`-filtered colimit of objects satisfying `P`.
We show that if this condition is satisfied, then `P` is a strong generator
(see `IsCardinalFilteredGenerator.isStrongGenerator`). Moreover,
if `C` is locally small, we show that any object in `C` is presentable
(see `IsCardinalFilteredGenerator.presentable`).

Finally, we define a typeclass `HasCardinalFilteredGenerator C κ` saying
that `C` is locally `w`-small and that there exists an (essentially) small `P`
such that `P.IsCardinalFilteredGenerator κ` holds.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits.ColimitPresentation

/-
**CategoryTheory.Limits.ColimitPresentation.isCardinalPresentable** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits.ColimitPresentation`。
形式化陈述：isCardinalPresentable {X : C} {J : Type w} [SmallCategory J] (p : ColimitP
resentation J X) (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : forall (j : J), IsCa
rdinalPresentable (p.diag.obj j) κ) [LocallySmall.{w} C] (κ' : Cardinal.{w}) [Fa
ct κ'.IsRegular] (h : κ <= κ') (hJ : HasCardinalLT (Arrow J) κ') : IsCardinalPre
sentable X κ'
参数：p : ColimitPresentation J X；κ : Cardinal.{w}；h : forall (j : J), IsCardinalPr
esentable (p.diag.obj j) κ；κ' : Cardinal.{w}；h : κ <= κ'；hJ : HasCardinalLT (Arr
ow J) κ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isCardinalPresentable_of_le`：isCardinalPresentable_of_le 
[IsCardinalPresentable X κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ <= κ'
) : IsCardinalPresentable X κ'
· 使用引理 `CategoryTheory.isCardinalPresentable_of_isColimit`：isCardinalPresentable
_of_isColimit [LocallySmall.{w} C] {K : Type u'} [Category.{v'} K] [HasLimitsOfS
hape Kᵒᵖ (Type w)] {Y : K ⥤ C} (c : Coc…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : ColimitPresentation J X) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ (j : J), IsCardinalPresentable (p.diag.obj j) κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  have (k : J) : IsCardinalPresentable (p.diag.obj k) κ' := isCardinalPresentable_of_le _ h
  isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end Limits.ColimitPresentation

open Limits

namespace ObjectProperty

variable {P : ObjectProperty C}

/-
**CategoryTheory.ObjectProperty.ColimitOfShape.isCardinalPresentable** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.ColimitOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.ObjectProperty C} {X : C} {J : Type w}   [inst_1 : CategoryTheory.SmallCatego
ry J] (p : P.ColimitOfShape J X) {κ : Cardinal.{w}} [inst_2 : Fact κ.IsRegular],
   P ≤ CategoryTheory.isCardinalPresentable C κ →     ∀ [CategoryTheory.LocallyS
mall.{w, v, u} C] (κ' : Cardinal.{w}) [inst_4 : Fact κ'.IsRegular],       κ ≤ κ'
 → HasCardinalLT (CategoryTheory.Arrow J) κ' → CategoryTheory.IsCardinalPresenta
ble X κ'
参数：p : P.ColimitOfShape J X；κ' : Cardinal.{w}；CategoryTheory.Arrow J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.ColimitPresentation.isCardinalPresentable`：isCardi
nalPresentable {X : C} {J : Type w} [SmallCategory J] (p : ColimitPresentation J
 X) (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : forall…
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma ColimitOfShape.isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : P.ColimitOfShape J X) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : P ≤ isCardinalPresentable C κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  p.toColimitPresentation.isCardinalPresentable κ
    (fun j ↦ hP _ (p.prop_diag_obj j)) _ h hJ

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (P κ) in
/-- The condition that `P : ObjectProperty C` consists of `κ`-presentable objects
and that any object of `C` is a `κ`-filtered colimit of objects satisfying `P`.
(This notion is particularly relevant when `C` is locally `w`-small and `P` is
essentially `w`-small, see `HasCardinalFilteredGenerators`, which appears in
the definitions of locally presentable and accessible categories.) -/
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator** 是 Mathlib 中的一个归纳类型
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.ObjectProperty C → (κ : Cardinal.{w}) → [Fact κ.IsRegular] → Prop
参数：κ : Cardinal.{w}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that `P : ObjectProperty C` consists of `κ`-presentable objects
and that any object of `C` is a `κ`-filtered colimit of objects satisfying `P`.
(This notion is particularly relevant when `C` is locally `w`-small and `P` is
essentially `w`-small, see `HasCardinalFilteredGenerators`, which appears in
the definitions of locally presentable and accessible categories.)
-/
structure IsCardinalFilteredGenerator : Prop where
  le_isCardinalPresentable : P ≤ isCardinalPresentable C κ
  exists_colimitsOfShape (X : C) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      P.colimitsOfShape J X

namespace IsCardinalFilteredGenerator

variable (h : P.IsCardinalFilteredGenerator κ) (X : C)

include h in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.of_le_isoClosure** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerato
r`。
形式化陈述：of_le_isoClosure {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure) (h₂ : P
' <= isCardinalPresentable C κ) : P'.IsCardinalFilteredGenerator κ where le_isCa
rdinalPresentable
参数：h₁ : P <= P'.isoClosure；h₂ : P' <= isCardinalPresentable C κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.exists_colimit
sOfShape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_isoClosure`：colimitsOfShap
e_isoClosure : P.isoClosure.colimitsOfShape J = P.colimitsOfShape J
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_monotone`：colimitsOfShape_
monotone {Q : ObjectProperty C} (hPQ : P <= Q) : P.colimitsOfShape J <= Q.colimi
tsOfShape J
-/
lemma of_le_isoClosure {P' : ObjectProperty C} (h₁ : P ≤ P'.isoClosure)
    (h₂ : P' ≤ isCardinalPresentable C κ) :
    P'.IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := h₂
  exists_colimitsOfShape X := by
    obtain ⟨J, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨J, inferInstance, inferInstance, by
      simpa only [colimitsOfShape_isoClosure] using colimitsOfShape_monotone J h₁ _ hX⟩

include h in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isoClosure** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator`。
形式化陈述：isoClosure : P.isoClosure.IsCardinalFilteredGenerator κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.of_le_isoClosu
re`：of_le_isoClosure {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure) (h₂ : P' 
<= isCardinalPresentable C κ) : P'.IsCardinalFilteredGenerator κ…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用定理 `CategoryTheory.instIsClosedUnderIsomorphismsIsCardinalPresentable`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (κ : Cardinal.{w}) [inst_
1 : Fact κ.IsRegular],   (CategoryTheory.isCardinalPres…
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
-/
lemma isoClosure : P.isoClosure.IsCardinalFilteredGenerator κ :=
  h.of_le_isoClosure (P.le_isoClosure.trans P.isoClosure.le_isoClosure)
    (by simpa only [ObjectProperty.isoClosure_le_iff] using h.le_isCardinalPresentable)
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isoClosure_iff** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator`
。
形式化陈述：isoClosure_iff : P.isoClosure.IsCardinalFilteredGenerator κ ↔ P.IsCardinal
FilteredGenerator κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.of_le_isoClosu
re`：of_le_isoClosure {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure) (h₂ : P' 
<= isCardinalPresentable C κ) : P'.IsCardinalFilteredGenerator κ…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isoClosure`：is
oClosure : P.isoClosure.IsCardinalFilteredGenerator κ
-/
lemma isoClosure_iff :
    P.isoClosure.IsCardinalFilteredGenerator κ ↔ P.IsCardinalFilteredGenerator κ :=
  ⟨fun h ↦ h.of_le_isoClosure (by rfl) (P.le_isoClosure.trans h.le_isCardinalPresentable),
    isoClosure⟩

include h in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.presentable** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator`。
形式化陈述：presentable [LocallySmall.{w} C] (X : C) : IsPresentable.{w} X
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.exists_colimit
sOfShape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用引理 `HasCardinalLT.exists_regular_cardinal_forall`：exists_regular_cardinal_fo
rall {ι : Type v} (X : ι -> Type u) [Small.{w} ι] [forall i, Small.{w} (X i)] : 
exists (κ : Cardinal.{w}), κ.IsReg…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.isCardinalPresentable`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectP
roperty C} {X : C} {J : Type w}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用引理 `CategoryTheory.isPresentable_of_isCardinalPresentable`：isPresentable_of_
isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalPresentab
le X κ] : IsPresentable.{w} X where exists_…
-/
lemma presentable [LocallySmall.{w} C] (X : C) :
    IsPresentable.{w} X := by
  obtain ⟨J, _, _, ⟨hX⟩⟩ := h.exists_colimitsOfShape X
  obtain ⟨κ', _, le, hκ'⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ ≤ κ'),
      HasCardinalLT (Arrow J) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) ↦ Arrow J) (fun (_ : Unit) ↦ κ.ord.ToType))
    exact ⟨κ', ⟨h₁⟩,
      le_of_lt (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h₂ (Sum.inr ⟨⟩)),
      h₂ (Sum.inl ⟨⟩)⟩
  have := hX.isCardinalPresentable h.le_isCardinalPresentable _ le hκ'
  exact isPresentable_of_isCardinalPresentable _ κ'

include h in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isStrongGenerator** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerat
or`。
形式化陈述：isStrongGenerator : P.IsStrongGenerator
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStrongGenerator.mk_of_exists_colimitsOfS
hape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.ObjectProperty C},   (∀ (X : C), ∃ J x, P.colimitsOfShape J X) …
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.exists_colimit
sOfShape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
-/
lemma isStrongGenerator : P.IsStrongGenerator :=
  IsStrongGenerator.mk_of_exists_colimitsOfShape.{w} (fun X ↦ by
    obtain ⟨_, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨_, _, hX⟩)

include h in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isPresentable_eq_ret
ractClosure** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalF
ilteredGenerator`。
形式化陈述：isPresentable_eq_retractClosure : isCardinalPresentable C κ = P.retractClo
sure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.exists_colimit
sOfShape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isCardinalPresentable_iff`：isCardinalPresentable_iff (X :
 C) : isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.instIsStableUnderRetractsIsCardinalPresentable`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}) [inst_1 : Fac
t κ.IsRegular],   (CategoryTheory.isCardinalPresent…
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
-/
lemma isPresentable_eq_retractClosure :
    isCardinalPresentable C κ = P.retractClosure := by
  refine le_antisymm (fun X hX ↦ ?_) ?_
  · rw [isCardinalPresentable_iff] at hX
    obtain ⟨J, _, _, ⟨p⟩⟩ := h.exists_colimitsOfShape X
    have := essentiallySmall_of_small_of_locallySmall.{w} J
    obtain ⟨j, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit (𝟙 X)
    exact ⟨_, p.prop_diag_obj j, ⟨{ i := _, r := _, retract := hf}⟩⟩
  · simpa only [ObjectProperty.retractClosure_le_iff] using h.le_isCardinalPresentable

include h in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.essentiallySmall_isP
resentable** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFi
lteredGenerator`。
形式化陈述：essentiallySmall_isPresentable [ObjectProperty.EssentiallySmall.{w} P] [Lo
callySmall.{w} C] : ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C
 κ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.isPresentable_
eq_retractClosure`：isPresentable_eq_retractClosure : isCardinalPresentable C κ =
 P.retractClosure
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallRetractClosureOfLocall
ySmall`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTh
eory.ObjectProperty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
-/
lemma essentiallySmall_isPresentable
    [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  rw [h.isPresentable_eq_retractClosure]
  infer_instance

end IsCardinalFilteredGenerator

end ObjectProperty

/-- The property that a category `C` and a regular cardinal `κ`
satisfy `P.IsCardinalFilteredGenerators κ` for a suitable essentially
small `P : ObjectProperty C`. -/
/-
**CategoryTheory.HasCardinalFilteredGenerator** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory`。
形式化陈述：(C : Type u) → [hC : CategoryTheory.Category.{v, u} C] → (κ : Cardinal.{w}
) → [hκ : Fact κ.IsRegular] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a category `C` and a regular cardinal `κ`
satisfy `P.IsCardinalFilteredGenerators κ` for a suitable essentially
small `P : ObjectProperty C`.
-/
class HasCardinalFilteredGenerator (C : Type u) [hC : Category.{v} C]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] : Prop extends LocallySmall.{w} C where
  exists_generator (C κ) [hC] [hκ] :
    ∃ (P : ObjectProperty C) (_ : ObjectProperty.EssentiallySmall.{w} P),
      P.IsCardinalFilteredGenerator κ
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredG
enerator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilt
eredGenerator`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.ObjectProperty C}   [CategoryTheory.ObjectProperty.EssentiallySmall.{w, v, u}
 P] [CategoryTheory.LocallySmall.{w, v, u} C]   {κ : Cardinal.{w}} [hκ : Fact κ.
IsRegular],   P.IsCardinalFilteredGenerator κ → CategoryTheory.HasCardinalFilter
edGenerator C κ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator
    {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    [LocallySmall.{w} C] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    (hP : P.IsCardinalFilteredGenerator κ) :
    HasCardinalFilteredGenerator C κ where
  exists_generator := ⟨P, inferInstance, hP⟩
/-
**CategoryTheory.HasCardinalFilteredGenerator.exists_small_generator** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.HasCardinalFilteredGenerator`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}
) [inst_1 : Fact κ.IsRegular]   [CategoryTheory.HasCardinalFilteredGenerator C κ
],   ∃ P, ∃ (_ : CategoryTheory.ObjectProperty.Small.{w, v, u} P), P.IsCardinalF
ilteredGenerator κ
参数：C : Type u；κ : Cardinal.{w}；_ : CategoryTheory.ObjectProperty.Small.{w, v, u}
 P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.exists_generator`：∀ (C : Typ
e u) [hC : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}) [hκ : Fact κ.IsR
egular]   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.of_le_isoClosu
re`：of_le_isoClosure {P' : ObjectProperty C} (h₁ : P <= P'.isoClosure) (h₂ : P' 
<= isCardinalPresentable C κ) : P'.IsCardinalFilteredGenerator κ…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.le_isCardinalP
resentable`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Catego
ryTheory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
-/
lemma HasCardinalFilteredGenerator.exists_small_generator (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasCardinalFilteredGenerator C κ] :
    ∃ (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P),
      P.IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  exact ⟨Q, inferInstance, hP.of_le_isoClosure h₂ (h₁.trans hP.le_isCardinalPresentable)⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasCardinalFilteredGenerator C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  exact hP.essentiallySmall_isPresentable

end CategoryTheory

