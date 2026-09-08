/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Images
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Facts about (co)limits of functors into concrete categories
-/

public section


universe s t w v u r

open CategoryTheory

namespace CategoryTheory.Types

open Limits

/-! The forgetful functor on `Type u` is the identity; copy the instances on `𝟭 (Type u)`
over to `forget Type u`.

Since instance synthesis only looks through reducible definitions, we need to help it out by copying
over the instances that wouldn't be found otherwise.
-/

/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor on `Type u` is the identity; copy the instances on `𝟭 (Typ
e u)`
over to `forget Type u`.

Since instance synthesis only looks through reducible definitions, we need to he
lp it out by copying
over the instances that wouldn't be found otherwise.
-/
instance : (forget <| Type u).Full :=
  Functor.Full.id
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfSize (forget <| Type u) :=
  id_preservesLimitsOfSize
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfSize (forget <| Type u) :=
  id_preservesColimitsOfSize
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ReflectsLimitsOfSize (forget <| Type u) :=
  id_reflectsLimits
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ReflectsColimitsOfSize (forget <| Type u) :=
  id_reflectsColimits
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget <| Type u).IsEquivalence :=
  Functor.isEquivalence_refl
/-
**CategoryTheory.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget <| Type u).IsCorepresentable :=
  inferInstanceAs (𝟭 <| Type u).IsCorepresentable

end CategoryTheory.Types

namespace CategoryTheory.Limits.Concrete

section Limits

/-- If a functor `G : J ⥤ C` to a concrete category has a limit and that `forget C`
is corepresentable, then `(G ⋙ forget C).sections` is small. -/
/-
**CategoryTheory.Limits.Concrete.small_sections_of_hasLimit** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：small_sections_of_hasLimit {C : Type u} [Category.{v} C] {FC : outParam <|
 C -> C -> Type*} {CC : outParam <| C -> Type v} [outParam <| forall X Y, FunLik
e (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [(forget C).IsCorepresenta
ble] {J : Type w} [Category.{t} J] (G : J ⥤ C) [HasLimit G] : Small.{v} (G ⋙ for
get C).sections
参数：FC X Y；CC X；CC Y；forget C；G : J ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Types.hasLimit_iff_small_sections`：hasLimit_iff_sm
all_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSize`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] (F : CategoryTheory.Functor C (Type u_1))   [
F.IsCorepresentable], CategoryTheory.L…

--- 原说明 ---
If a functor `G : J ⥤ C` to a concrete category has a limit and that `forget C`
is corepresentable, then `(G ⋙ forget C).sections` is small.
-/
lemma small_sections_of_hasLimit
    {C : Type u} [Category.{v} C] {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type v}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [(forget C).IsCorepresentable] {J : Type w} [Category.{t} J] (G : J ⥤ C) [HasLimit G] :
    Small.{v} (G ⋙ forget C).sections := by
  rw [← Types.hasLimit_iff_small_sections]
  infer_instance

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type r}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{r} C FC]
variable {J : Type w} [Category.{t} J] (F : J ⥤ C) [PreservesLimit F (forget C)]
/-
**CategoryTheory.Limits.Concrete.to_product_injective_of_isLimit** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：to_product_injective_of_isLimit {D : Cone F} (hD : IsLimit D) : Function.I
njective fun (x : ToType D.pt) (j : J) => D.π.app j x
参数：hD : IsLimit D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem to_product_injective_of_isLimit
    {D : Cone F} (hD : IsLimit D) :
    Function.Injective fun (x : ToType D.pt) (j : J) => D.π.app j x := by
  let E := (forget C).mapCone D
  intro (x : E.pt) y H
  apply (Types.isLimitEquivSections (isLimitOfPreserves _ hD)).injective
  ext j
  exact funext_iff.mp H j
/-
**CategoryTheory.Limits.Concrete.isLimit_ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Concrete`。
形式化陈述：isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : ToType D.pt) : (forall j,
 D.π.app j x = D.π.app j y) -> x = y
参数：hD : IsLimit D；x y : ToType D.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.to_product_injective_of_isLimit`：to_produ
ct_injective_of_isLimit {D : Cone F} (hD : IsLimit D) : Function.Injective fun (
x : ToType D.pt) (j : J) => D.π.app j x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : ToType D.pt) :
    (∀ j, D.π.app j x = D.π.app j y) → x = y := fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)
/-
**CategoryTheory.Limits.Concrete.limit_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.Concrete`。
形式化陈述：limit_ext [HasLimit F] (x y : ToType (limit F)) : (forall j, limit.π F j x
 = limit.π F j y) -> x = y
参数：x y : ToType (limit F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.isLimit_ext`：isLimit_ext {D : Cone F} (hD
 : IsLimit D) (x y : ToType D.pt) : (forall j, D.π.app j x = D.π.app j y) -> x =
 y
-/
theorem limit_ext [HasLimit F] (x y : ToType (limit F)) :
    (∀ j, limit.π F j x = limit.π F j y) → x = y :=
  Concrete.isLimit_ext F (limit.isLimit _) _ _

section Surjective

/--
Given surjections `⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀` in a concrete category whose forgetful functor
preserves sequential limits, the projection map `lim Xₙ ⟶ X₀` is surjective.
-/
/-
**CategoryTheory.Limits.Concrete.surjective_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits.Concrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given surjections `⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀` in a concrete category whose forgetfu
l functor
preserves sequential limits, the projection map `lim Xₙ ⟶ X₀` is surjective.
-/
lemma surjective_π_app_zero_of_surjective_map {C : Type u} [Category.{v} C] {FC : C → C → Type*}
    {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [PreservesLimitsOfShape ℕᵒᵖ (forget C)] {F : ℕᵒᵖ ⥤ C} {c : Cone F}
    (hc : IsLimit c) (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) :=
  Types.surjective_π_app_zero_of_surjective_map (isLimitOfPreserves (forget C) hc) hF

end Surjective

end Limits

section Colimits

section

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type t}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{t} C FC]
variable {J : Type w} [Category.{r} J] (F : J ⥤ C)

section
variable [PreservesColimit F (forget C)]

/-
**CategoryTheory.Limits.Concrete.from_union_surjective_of_isColimit** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) : let
 ff : (Σ j : J, ToType (F.obj j)) -> ToType D.pt
参数：hD : IsColimit D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
-/
theorem from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σ j : J, ToType (F.obj j)) → ToType D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff x
  let E : Cocone (F ⋙ forget C) := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves (forget C) hD
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hE x
  exact ⟨⟨j, y⟩, hy⟩
/-
**CategoryTheory.Limits.Concrete.isColimit_exists_rep** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Concrete`。
形式化陈述：isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt) :
 exists (j : J) (y : ToType (F.obj j)), D.ι.app j y = x
参数：hD : IsColimit D；x : ToType D.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.from_union_surjective_of_isColimit`：from_
union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) : let ff : (Σ j 
: J, ToType (F.obj j)) -> ToType D.pt
-/
theorem isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt) :
    ∃ (j : J) (y : ToType (F.obj j)), D.ι.app j y = x := by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩
/-
**CategoryTheory.Limits.Concrete.colimit_exists_rep** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.Concrete`。
形式化陈述：colimit_exists_rep [HasColimit F] (x : ToType (colimit F)) : exists (j : J
) (y : ToType (F.obj j)), colimit.ι F j y = x
参数：x : ToType (colimit F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.isColimit_exists_rep`：isColimit_exists_re
p {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt) : exists (j : J) (y : ToTy
pe (F.obj j)), D.ι.app j y = x
-/
theorem colimit_exists_rep [HasColimit F] (x : ToType (colimit F)) :
    ∃ (j : J) (y : ToType (F.obj j)), colimit.ι F j y = x :=
  Concrete.isColimit_exists_rep F (colimit.isColimit _) x

end

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Concrete.isColimit_rep_eq_of_exists** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (x : ToType (F.obj i))
 (y : ToType (F.obj j)) (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x =
 F.map g y) : D.ι.app i x = D.ι.app j y
参数：x : ToType (F.obj i)；y : ToType (F.obj j)；h : exists (k : _) (f : i ⟶ k) (g :
 j ⟶ k), F.map f x = F.map g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
theorem isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j))
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  let E := (forget C).mapCocone D
  obtain ⟨k, f, g, (hfg : (F ⋙ forget C).map f x = F.map g y)⟩ := h
  let h1 : (F ⋙ forget C).map f ≫ E.ι.app k = E.ι.app i := E.ι.naturality f
  let h2 : (F ⋙ forget C).map g ≫ E.ι.app k = E.ι.app j := E.ι.naturality g
  change E.ι.app i x = E.ι.app j y
  rw [← h1, comp_apply, hfg]
  exact ConcreteCategory.congr_hom h2 y
/-
**CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : ToType (F.obj i)) (
y : ToType (F.obj j)) (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F
.map g y) : colimit.ι F i x = colimit.ι F j y
参数：x : ToType (F.obj i)；y : ToType (F.obj j)；h : exists (k : _) (f : i ⟶ k) (g :
 j ⟶ k), F.map f x = F.map g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.isColimit_rep_eq_of_exists`：isColimit_rep
_eq_of_exists {D : Cocone F} {i j : J} (x : ToType (F.obj i)) (y : ToType (F.obj
 j)) (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k…
-/
theorem colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j))
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.isColimit_rep_eq_of_exists F x y h

end

section FilteredColimits

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type s}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {J : Type w} [Category.{r} J] (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J]

/-
**CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D) (x 
: ToType (F.obj i)) (y : ToType (F.obj j)) (h : D.ι.app _ x = D.ι.app _ y) : exi
sts (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y
参数：hD : IsColimit D；x : ToType (F.obj i)；y : ToType (F.obj j)；h : D.ι.app _ x = 
D.ι.app _ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`：isColimit_
eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j}
 : t.ι.app i xi = t.ι.app j xj ↔ exists (k : _) (f…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
-/
theorem isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : ToType (F.obj i)) (y : ToType (F.obj j)) (h : D.ι.app _ x = D.ι.app _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  exact (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget C) hE).mp h
/-
**CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D) (x
 : ToType (F.obj i)) (y : ToType (F.obj j)) : D.ι.app i x = D.ι.app j y ↔ exists
 (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y
参数：hD : IsColimit D；x : ToType (F.obj i)；y : ToType (F.obj j)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq`：isColimit_exi
sts_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D) (x : ToType (F.obj i))
 (y : ToType (F.obj j)) (h : D.ι.app _ x = D.ι.…
· 使用定理 `CategoryTheory.Limits.Concrete.isColimit_rep_eq_of_exists`：isColimit_rep
_eq_of_exists {D : Cocone F} {i j : J} (x : ToType (F.obj i)) (y : ToType (F.obj
 j)) (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k…
-/
theorem isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : ToType (F.obj i)) (y : ToType (F.obj j)) :
    D.ι.app i x = D.ι.app j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq.{s} _ hD _ _,
   Concrete.isColimit_rep_eq_of_exists _ _ _⟩
/-
**CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : ToType (F.obj i)) (
y : ToType (F.obj j)) (h : colimit.ι F _ x = colimit.ι F _ y) : exists (k : _) (
f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y
参数：x : ToType (F.obj i)；y : ToType (F.obj j)；h : colimit.ι F _ x = colimit.ι F _
 y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq`：isColimit_exi
sts_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D) (x : ToType (F.obj i))
 (y : ToType (F.obj j)) (h : D.ι.app _ x = D.ι.…
-/
theorem colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j)) (h : colimit.ι F _ x = colimit.ι F _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq.{s} F (colimit.isColimit _) x y h
/-
**CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : ToType (F.obj i)) 
(y : ToType (F.obj j)) : colimit.ι F i x = colimit.ι F j y ↔ exists (k : _) (f :
 i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y
参数：x : ToType (F.obj i)；y : ToType (F.obj j)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq`：colimit_exists_
of_rep_eq [HasColimit F] {i j : J} (x : ToType (F.obj i)) (y : ToType (F.obj j))
 (h : colimit.ι F _ x = colimit.ι F _ y) : ex…
· 使用定理 `CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists`：colimit_rep_eq_
of_exists [HasColimit F] {i j : J} (x : ToType (F.obj i)) (y : ToType (F.obj j))
 (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k),…
-/
theorem colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j)) :
    colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq.{s} _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩

set_option backward.defeqAttrib.useBackward true in
omit [IsFiltered J] in
/-
**CategoryTheory.Limits.Concrete.exists_hom_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Concrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_hom_ι_eq_of_isColimit [IsFilteredOrEmpty J] {D : Cocone F} (hD : IsColimit D)
    (x : ToType D.pt) (k : J) :
    ∃ (j : J) (_ : k ⟶ j) (y : ToType (F.obj j)), D.ι.app j y = x := by
  obtain ⟨j, y, rfl⟩ := isColimit_exists_rep F hD x
  refine ⟨IsFiltered.max k j, IsFiltered.leftToMax _ _, F.map (IsFiltered.rightToMax _ _) y, ?_⟩
  rw [← ConcreteCategory.comp_apply]
  congr 1
  simp

end FilteredColimits

end Colimits

end CategoryTheory.Limits.Concrete

