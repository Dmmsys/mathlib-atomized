/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Limits in concrete categories

In this file, we combine the description of limits in `Types` and the API about
the preservation of products and pullbacks in order to describe these limits in a
concrete category `C`.

If `F : J → C` is a family of objects in `C`, we define a bijection
`Limits.Concrete.productEquiv F : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)`.

Similarly, if `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` are two morphisms, the elements
in `pullback f₁ f₂` are identified by `Limits.Concrete.pullbackEquiv`
to compatible tuples of elements in `X₁ × X₂`.

Some results are also obtained for the terminal object, binary products,
wide-pullbacks, wide-pushouts, multiequalizers and cokernels.

-/

@[expose] public section

universe s w w' v u t r

namespace CategoryTheory.Limits.Concrete

open ConcreteCategory

variable {C : Type u} [Category.{v} C]

section Products

section ProductEquiv

variable {FC : C → C → Type*} {CC : C → Type max w v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{max w v} C FC] {J : Type w} (F : J → C)
  [HasProduct F] [PreservesLimit (Discrete.functor F) (forget C)]

/-- The equivalence `ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)` if `F : J → C` is a family of objects
in a concrete category `C`. -/
/-
**CategoryTheory.Limits.Concrete.productEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Concrete`。
形式化陈述：productEquiv : ToType (∏ᶜ F) ≃ forall j, ToType (F j)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)` if `F : J → C` is a family o
f objects
in a concrete category `C`.
-/
noncomputable def productEquiv : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j) :=
  ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} fun j =>
    (ToType (F j)))).toEquiv

@[simp]
/-
**CategoryTheory.Limits.Concrete.productEquiv_apply_apply** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：productEquiv_apply_apply (x : ToType (∏ᶜ F)) (j : J) : productEquiv F x j 
= Pi.π F j x
参数：x : ToType (∏ᶜ F)；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π`：piComparison_comp_π [HasProdu
ct f] [HasProduct fun b => G.obj (f b)] (b : β) : piComparison G f ≫ Pi.π _ b = 
G.map (Pi.π f b)
-/
lemma productEquiv_apply_apply (x : ToType (∏ᶜ F)) (j : J) :
    productEquiv F x j = Pi.π F j x :=
  congr_hom (piComparison_comp_π (forget C) F j) x

@[simp]
/-
**CategoryTheory.Limits.Concrete.productEquiv_symm_apply_** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.Concrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma productEquiv_symm_apply_π (x : ∀ j, ToType (F j)) (j : J) :
    Pi.π F j ((productEquiv F).symm x) = x j := by
  rw [← productEquiv_apply_apply, Equiv.apply_symm_apply]

end ProductEquiv

section ProductExt

variable {J : Type w} (f : J → C) [HasProduct f] {D : Type t} [Category.{r} D]
variable {FD : D → D → Type*} {DD : D → Type max w r} [∀ X Y, FunLike (FD X Y) (DD X) (DD Y)]
variable [ConcreteCategory.{max w r} D FD] (F : C ⥤ D)
  [PreservesLimit (Discrete.functor f) F]
  [HasProduct fun j => F.obj (f j)]
  [PreservesLimitsOfShape WalkingCospan (forget D)]
  [PreservesLimit (Discrete.functor fun b ↦ F.obj (f b)) (forget D)]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Concrete.Pi.map_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Concrete.Pi`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} (f :
 J → C)   [inst_1 : CategoryTheory.Limits.HasProduct f] {D : Type t} [inst_2 : C
ategoryTheory.Category.{r, t} D]   {FD : D → D → Type u_1} {DD : D → Type (max w
 r)} [inst_3 : (X Y : D) → FunLike (FD X Y) (DD X) (DD Y)]   [inst_4 : CategoryT
heory.ConcreteCategory D FD] (F : CategoryTheory.Functor C D)   [CategoryTheory.
Limits.PreservesLimit (CategoryTheory.Discrete.functor f) F]   [CategoryTheory.L
imits.HasProduct fun j => F.obj (f j)]   [CategoryTheory.Limits.PreservesLimitsO
fShape CategoryTheory.Limits.WalkingCospan (CategoryTheory.forget D)]   [Categor
yTheory.Limits.PreservesLimit (CategoryTheory.Discrete.functor fun b => F.obj (f
 b))       (CategoryTheory.forget D)]   (x y : CategoryTheory.ToType (F.obj (∏ᶜ 
f))),   (∀ (i : J),       (CategoryTheory.ConcreteCategory.hom (F.map (CategoryT
heory.Limits.Pi.π f i))) x =         (CategoryTheory.ConcreteCategory.hom (F.map
 (CategoryTheory.Limits.Pi.π f i))) y) →     x = y
参数：f : J → C；max w r；X Y : D；FD X Y；DD X；DD Y；F : CategoryTheory.Functor C D；Cat
egoryTheory.Discrete.functor f；f j；CategoryTheory.forget D；CategoryTheory.Discre
te.functor fun b => F.obj (f b)；CategoryTheory.forget D；x y : CategoryTheory.ToT
ype (F.obj (∏ᶜ f))；∀ (i : J),       (CategoryTheory.ConcreteCategory.hom (F.map 
(CategoryTheory.Limits.Pi.π f i))) x =         (CategoryTheory.ConcreteCategory.
hom (F.map (CategoryTheory.Limits.Pi.π f i))) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback`：
injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f] [Preserves
LimitsOfShape WalkingCospan (forget C)] : Function.Injective…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.Concrete.limit_ext`：limit_ext [HasLimit F] (x y : 
ToType (limit F)) : (forall j, limit.π F j x = limit.π F j y) -> x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π`：piComparison_comp_π [HasProdu
ct f] [HasProduct fun b => G.obj (f b)] (b : β) : piComparison G f ≫ Pi.π _ b = 
G.map (Pi.π f b)
-/
lemma Pi.map_ext (x y : ToType (F.obj (∏ᶜ f : C)))
    (h : ∀ i, F.map (Pi.π f i) x = F.map (Pi.π f i) y) : x = y := by
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (PreservesProduct.iso F f).hom
  apply Concrete.limit_ext _ (piComparison F _ x) (piComparison F _ y)
  intro ⟨j⟩
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, piComparison_comp_π]
  exact h j

end ProductExt

end Products

section Terminal

variable {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC]

/-- If `forget C` preserves terminals and `X` is terminal, then `ToType X` is a
singleton. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.Concrete.uniqueOfTerminalOfPreserves** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：uniqueOfTerminalOfPreserves [PreservesLimit (Functor.empty.{0} C) (forget 
C)] (X : C) (h : IsTerminal X) : Unique (ToType X)
参数：Functor.empty.{0} C；forget C；X : C；h : IsTerminal X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `forget C` preserves terminals and `X` is terminal, then `ToType X` is a
singleton.
-/
noncomputable def uniqueOfTerminalOfPreserves [PreservesLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : IsTerminal X) : Unique (ToType X) :=
  Types.isTerminalEquivUnique (ToType X) <| IsTerminal.isTerminalObj (forget C) X h

/-- If `forget C` reflects terminals and `ToType X` is a singleton, then `X` is terminal. -/
/-
**CategoryTheory.Limits.Concrete.terminalOfUniqueOfReflects** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：terminalOfUniqueOfReflects [ReflectsLimit (Functor.empty.{0} C) (forget C)
] (X : C) (h : Unique (ToType X)) : IsTerminal X
参数：Functor.empty.{0} C；forget C；X : C；h : Unique (ToType X)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `forget C` reflects terminals and `ToType X` is a singleton, then `X` is term
inal.
-/
noncomputable def terminalOfUniqueOfReflects [ReflectsLimit (Functor.empty.{0} C) (forget C)]
    (X : C) (h : Unique (ToType X)) : IsTerminal X :=
  IsTerminal.isTerminalOfObj (forget C) X <|
    (Types.isTerminalEquivUnique (ToType X)).symm h

/-- The equivalence `IsTerminal X ≃ Unique (ToType X)` if the forgetful functor
preserves and reflects terminals. -/
/-
**CategoryTheory.Limits.Concrete.terminalIffUnique** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Concrete`。
形式化陈述：terminalIffUnique [PreservesLimit (Functor.empty.{0} C) (forget C)] [Refle
ctsLimit (Functor.empty.{0} C) (forget C)] (X : C) : IsTerminal X ≃ Unique (ToTy
pe X)
参数：Functor.empty.{0} C；forget C；Functor.empty.{0} C；forget C；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence `IsTerminal X ≃ Unique (ToType X)` if the forgetful functor
preserves and reflects terminals.
-/
noncomputable def terminalIffUnique [PreservesLimit (Functor.empty.{0} C) (forget C)]
    [ReflectsLimit (Functor.empty.{0} C) (forget C)] (X : C) :
    IsTerminal X ≃ Unique (ToType X) :=
  (IsTerminal.isTerminalIffObj (forget C) X).trans <| Types.isTerminalEquivUnique _

variable (C)
variable [HasTerminal C] [PreservesLimit (Functor.empty.{0} C) (forget C)]

/-- The equivalence `ToType (⊤_ C) ≃ PUnit` when `C` is a concrete category. -/
/-
**CategoryTheory.Limits.Concrete.terminalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Concrete`。
形式化陈述：terminalEquiv : ToType (⊤_ C) ≃ PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `ToType (⊤_ C) ≃ PUnit` when `C` is a concrete category.
-/
noncomputable def terminalEquiv : ToType (⊤_ C) ≃ PUnit :=
  (PreservesTerminal.iso (forget C) ≪≫ Types.terminalIso).toEquiv
/-
**CategoryTheory.Limits.Concrete.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limi
ts.Concrete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Unique (ToType (⊤_ C)) where
  default := (terminalEquiv C).symm PUnit.unit
  uniq _ := (terminalEquiv C).injective (Subsingleton.elim _ _)

end Terminal

section Initial

variable {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC]

/-- If `forget C` preserves initials and `X` is initial, then `ToType X` is empty. -/
/-
**CategoryTheory.Limits.Concrete.empty_of_initial_of_preserves** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：empty_of_initial_of_preserves [PreservesColimit (Functor.empty.{0} C) (for
get C)] (X : C) (h : Nonempty (IsInitial X)) : IsEmpty (ToType X)
参数：Functor.empty.{0} C；forget C；X : C；h : Nonempty (IsInitial X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.Types.initial_iff_empty`：initial_iff_empty (X : Ty
pe u) : Nonempty (IsInitial X) ↔ IsEmpty X
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
If `forget C` preserves initials and `X` is initial, then `ToType X` is empty.
-/
lemma empty_of_initial_of_preserves [PreservesColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : Nonempty (IsInitial X)) : IsEmpty (ToType X) := by
  rw [← Types.initial_iff_empty]
  exact Nonempty.map (IsInitial.isInitialObj (forget C) _) h

/-- If `forget C` reflects initials and `ToType X` is empty, then `X` is initial. -/
/-
**CategoryTheory.Limits.Concrete.initial_of_empty_of_reflects** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：initial_of_empty_of_reflects [ReflectsColimit (Functor.empty.{0} C) (forge
t C)] (X : C) (h : IsEmpty (ToType X)) : Nonempty (IsInitial X)
参数：Functor.empty.{0} C；forget C；X : C；h : IsEmpty (ToType X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Limits.Types.initial_iff_empty`：initial_iff_empty (X : Ty
pe u) : Nonempty (IsInitial X) ↔ IsEmpty X

--- 原说明 ---
If `forget C` reflects initials and `ToType X` is empty, then `X` is initial.
-/
lemma initial_of_empty_of_reflects [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C)
    (h : IsEmpty (ToType X)) : Nonempty (IsInitial X) :=
  Nonempty.map (IsInitial.isInitialOfObj (forget C) _) <|
    (Types.initial_iff_empty (ToType X)).mpr h

/-- If `forget C` preserves and reflects initials, then `X` is initial if and only if
`ToType X` is empty. -/
/-
**CategoryTheory.Limits.Concrete.initial_iff_empty_of_preserves_of_reflects** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：initial_iff_empty_of_preserves_of_reflects [PreservesColimit (Functor.empt
y.{0} C) (forget C)] [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C) 
: Nonempty (IsInitial X) ↔ IsEmpty (ToType X)
参数：Functor.empty.{0} C；forget C；Functor.empty.{0} C；forget C；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.Types.initial_iff_empty`：initial_iff_empty (X : Ty
pe u) : Nonempty (IsInitial X) ↔ IsEmpty X
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `forget C` preserves and reflects initials, then `X` is initial if and only i
f
`ToType X` is empty.
-/
lemma initial_iff_empty_of_preserves_of_reflects [PreservesColimit (Functor.empty.{0} C) (forget C)]
    [ReflectsColimit (Functor.empty.{0} C) (forget C)] (X : C) :
    Nonempty (IsInitial X) ↔ IsEmpty (ToType X) := by
  rw [← Types.initial_iff_empty, (IsInitial.isInitialIffObj (forget C) X).nonempty_congr]

end Initial

section BinaryProducts

variable {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{w} C FC] (X₁ X₂ : C) [HasBinaryProduct X₁ X₂]
  [PreservesLimit (pair X₁ X₂) (forget C)]

/-- The equivalence `ToType (X₁ ⨯ X₂) ≃ (ToType X₁) × (ToType X₂)`
if `X₁` and `X₂` are objects in a concrete category `C`. -/
/-
**CategoryTheory.Limits.Concrete.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Concrete`。
形式化陈述：prodEquiv : ToType (X₁ ⨯ X₂) ≃ ToType X₁ × ToType X₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `ToType (X₁ ⨯ X₂) ≃ (ToType X₁) × (ToType X₂)`
if `X₁` and `X₂` are objects in a concrete category `C`.
-/
noncomputable def prodEquiv : ToType (X₁ ⨯ X₂) ≃ ToType X₁ × ToType X₂ :=
  (PreservesLimitPair.iso (forget C) X₁ X₂ ≪≫ Types.binaryProductIso _ _).toEquiv

@[simp]
/-
**CategoryTheory.Limits.Concrete.prodEquiv_apply_fst** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.Concrete`。
形式化陈述：prodEquiv_apply_fst (x : ToType (X₁ ⨯ X₂)) : (prodEquiv X₁ X₂ x).fst = (Li
mits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) x
参数：x : ToType (X₁ ⨯ X₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.prodComparison_fst`：prodComparison_fst : prodCompa
rison F A B ≫ prod.fst = F.map prod.fst
-/
lemma prodEquiv_apply_fst (x : ToType (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).fst = (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) x := by
  simpa using! congr_hom (prodComparison_fst (forget C) X₁ X₂) x

@[simp]
/-
**CategoryTheory.Limits.Concrete.prodEquiv_apply_snd** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.Concrete`。
形式化陈述：prodEquiv_apply_snd (x : ToType (X₁ ⨯ X₂)) : (prodEquiv X₁ X₂ x).snd = (Li
mits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) x
参数：x : ToType (X₁ ⨯ X₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.prodComparison_snd`：prodComparison_snd : prodCompa
rison F A B ≫ prod.snd = F.map prod.snd
-/
lemma prodEquiv_apply_snd (x : ToType (X₁ ⨯ X₂)) :
    (prodEquiv X₁ X₂ x).snd = (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) x := by
  simpa using! congr_hom (prodComparison_snd (forget C) X₁ X₂) x

@[simp]
/-
**CategoryTheory.Limits.Concrete.prodEquiv_symm_apply_fst** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：prodEquiv_symm_apply_fst (x : ToType X₁ × ToType X₂) : (Limits.prod.fst : 
X₁ ⨯ X₂ ⟶ X₁) ((prodEquiv X₁ X₂).symm x) = x.1
参数：x : ToType X₁ × ToType X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.Limits.Concrete.prodEquiv_apply_fst`：prodEquiv_apply_fst 
(x : ToType (X₁ ⨯ X₂)) : (prodEquiv X₁ X₂ x).fst = (Limits.prod.fst : X₁ ⨯ X₂ ⟶ 
X₁) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodEquiv_symm_apply_fst (x : ToType X₁ × ToType X₂) :
    (Limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁) ((prodEquiv X₁ X₂).symm x) = x.1 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

@[simp]
/-
**CategoryTheory.Limits.Concrete.prodEquiv_symm_apply_snd** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：prodEquiv_symm_apply_snd (x : ToType X₁ × ToType X₂) : (Limits.prod.snd : 
X₁ ⨯ X₂ ⟶ X₂) ((prodEquiv X₁ X₂).symm x) = x.2
参数：x : ToType X₁ × ToType X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.Limits.Concrete.prodEquiv_apply_snd`：prodEquiv_apply_snd 
(x : ToType (X₁ ⨯ X₂)) : (prodEquiv X₁ X₂ x).snd = (Limits.prod.snd : X₁ ⨯ X₂ ⟶ 
X₂) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodEquiv_symm_apply_snd (x : ToType X₁ × ToType X₂) :
    (Limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) ((prodEquiv X₁ X₂).symm x) = x.2 := by
  obtain ⟨y, rfl⟩ := (prodEquiv X₁ X₂).surjective x
  simp

end BinaryProducts

section Pullbacks

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]
variable {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] [PreservesLimit (cospan f₁ f₂) (forget C)]

/-- In a concrete category `C`, given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`,
the elements in `pullback f₁ f₂` can be identified to compatible tuples of
elements in `X₁` and `X₂`. -/
/-
**CategoryTheory.Limits.Concrete.pullbackEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Concrete`。
形式化陈述：pullbackEquiv : ToType (pullback f₁ f₂) ≃ { p : ToType X₁ × ToType X₂ // f
₁ p.1 = f₂ p.2 }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a concrete category `C`, given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`,
the elements in `pullback f₁ f₂` can be identified to compatible tuples of
elements in `X₁` and `X₂`.
-/
noncomputable def pullbackEquiv :
    ToType (pullback f₁ f₂) ≃ { p : ToType X₁ × ToType X₂ // f₁ p.1 = f₂ p.2 } :=
  (PreservesPullback.iso (forget C) f₁ f₂ ≪≫
    Types.pullbackIsoPullback (↾f₁) (↾f₂)).toEquiv

/-- Constructor for elements in a pullback in a concrete category. -/
/-
**CategoryTheory.Limits.Concrete.pullbackMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Concrete`。
形式化陈述：pullbackMk (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) : ToType 
(pullback f₁ f₂)
参数：x₁ : ToType X₁；x₂ : ToType X₂；h : f₁ x₁ = f₂ x₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for elements in a pullback in a concrete category.
-/
noncomputable def pullbackMk (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    ToType (pullback f₁ f₂) :=
  (pullbackEquiv f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩
/-
**CategoryTheory.Limits.Concrete.pullbackMk_surjective** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits.Concrete`。
形式化陈述：pullbackMk_surjective (x : ToType (pullback f₁ f₂)) : exists (x₁ : ToType 
X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂), x = pullbackMk f₁ f₂ x₁ x₂ h
参数：x : ToType (pullback f₁ f₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
lemma pullbackMk_surjective (x : ToType (pullback f₁ f₂)) :
    ∃ (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂), x = pullbackMk f₁ f₂ x₁ x₂ h := by
  obtain ⟨⟨⟨x₁, x₂⟩, h⟩, rfl⟩ := (pullbackEquiv f₁ f₂).symm.surjective x
  exact ⟨x₁, x₂, h, rfl⟩

@[simp]
/-
**CategoryTheory.Limits.Concrete.pullbackMk_fst** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.Concrete`。
形式化陈述：pullbackMk_fst (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) : pul
lback.fst f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₁
参数：x₁ : ToType X₁；x₂ : ToType X₂；h : f₁ x₁ = f₂ x₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_inv_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.pullbackIsoPullback_inv_fst`：∀ {X Y Z : Type
 u} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.Types.pullbackIsoPullback f g).inv  …
-/
lemma pullbackMk_fst (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    pullback.fst f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₁ :=
  (congr_hom (PreservesPullback.iso_inv_fst (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_fst (↾f₁) (↾f₂)) _)

@[simp]
/-
**CategoryTheory.Limits.Concrete.pullbackMk_snd** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits.Concrete`。
形式化陈述：pullbackMk_snd (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) : pul
lback.snd f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₂
参数：x₁ : ToType X₁；x₂ : ToType X₂；h : f₁ x₁ = f₂ x₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_inv_snd`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.pullbackIsoPullback_inv_snd`：∀ {X Y Z : Type
 u} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.Types.pullbackIsoPullback f g).inv  …
-/
lemma pullbackMk_snd (x₁ : ToType X₁) (x₂ : ToType X₂) (h : f₁ x₁ = f₂ x₂) :
    pullback.snd f₁ f₂ (pullbackMk f₁ f₂ x₁ x₂ h) = x₂ :=
  (congr_hom (PreservesPullback.iso_inv_snd (forget C) f₁ f₂) _).trans
    (congr_hom (Types.pullbackIsoPullback_inv_snd (↾f₁) (↾f₂)) _)

end Pullbacks

section WidePullback

variable {FC : C → C → Type*} {CC : C → Type (max v w)} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{max v w} C FC]

open WidePullback

open WidePullbackShape

/-
**CategoryTheory.Limits.Concrete.widePullback_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Concrete`。
形式化陈述：widePullback_ext {B : C} {ι : Type w} {X : ι -> C} (f : forall j : ι, X j 
⟶ B) [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)] (x y
 : ToType (widePullback B X f)) (h₀ : base f x = base f y) (h : forall j, π f j 
x = π f j y) : x = y
参数：f : forall j : ι, X j ⟶ B；wideCospan B X f；forget C；x y : ToType (widePullbac
k B X f)；h₀ : base f x = base f y；h : forall j, π f j x = π f j y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.limit_ext`：limit_ext [HasLimit F] (x y : 
ToType (limit F)) : (forall j, limit.π F j x = limit.π F j y) -> x = y
-/
theorem widePullback_ext {B : C} {ι : Type w} {X : ι → C} (f : ∀ j : ι, X j ⟶ B)
    [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)]
    (x y : ToType (widePullback B X f)) (h₀ : base f x = base f y) (h : ∀ j, π f j x = π f j y) :
    x = y := by
  apply Concrete.limit_ext
  rintro (_ | j)
  · exact h₀
  · apply h
/-
**CategoryTheory.Limits.Concrete.widePullback_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.Concrete`。
形式化陈述：widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι -> C} (f : fora
ll j : ι, X j ⟶ B) [HasWidePullback.{w} B X f] [PreservesLimit (wideCospan B X f
) (forget C)] (x y : ToType (widePullback B X f)) (h : forall j, π f j x = π f j
 y) : x = y
参数：f : forall j : ι, X j ⟶ B；wideCospan B X f；forget C；x y : ToType (widePullbac
k B X f)；h : forall j, π f j x = π f j y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.widePullback_ext`：widePullback_ext {B : C
} {ι : Type w} {X : ι -> C} (f : forall j : ι, X j ⟶ B) [HasWidePullback B X f] 
[PreservesLimit (wideCospan B X f) (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.WidePullback.π_arrow`：π_arrow (j : J) : π arrows j
 ≫ arrows _ = base arrows
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι → C}
    (f : ∀ j : ι, X j ⟶ B) [HasWidePullback.{w} B X f]
    [PreservesLimit (wideCospan B X f) (forget C)] (x y : ToType (widePullback B X f))
    (h : ∀ j, π f j x = π f j y) : x = y := by
  apply Concrete.widePullback_ext _ _ _ _ h
  inhabit ι
  simp only [← π_arrow f default, ConcreteCategory.comp_apply, h]

end WidePullback

section Multiequalizer

variable {FC : C → C → Type*} {CC : C → Type s} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{s} C FC]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Concrete.multiequalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.Concrete`。
形式化陈述：multiequalizer_ext {J : MulticospanShape.{w, w'}} {I : MulticospanIndex J 
C} [HasMultiequalizer I] [PreservesLimit I.multicospan (forget C)] (x y : ToType
 (multiequalizer I)) (h : forall t : J.L, Multiequalizer.ι I t x = Multiequalize
r.ι I t y) : x = y
参数：forget C；x y : ToType (multiequalizer I)；h : forall t : J.L, Multiequalizer.ι
 I t x = Multiequalizer.ι I t y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.limit_ext`：limit_ext [HasLimit F] (x y : 
ToType (limit F)) : (forall j, limit.π F j x = limit.π F j y) -> x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multiequalizer_ext {J : MulticospanShape.{w, w'}}
    {I : MulticospanIndex J C} [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x y : ToType (multiequalizer I))
    (h : ∀ t : J.L, Multiequalizer.ι I t x = Multiequalizer.ι I t y) : x = y := by
  apply Concrete.limit_ext
  rintro (a | b)
  · apply h
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    simp [h]

set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary equivalence to be used in `multiequalizerEquiv` below. -/
/-
**CategoryTheory.Limits.Concrete.multiequalizerEquivAux** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Concrete`。
形式化陈述：multiequalizerEquivAux {J : MulticospanShape.{w, w'}} (I : MulticospanInde
x J C) : (I.multicospan ⋙ forget C).sections ≃ { x : forall i : J.L, ToType (I.l
eft i) // forall i : J.R, I.fst i (x _) = I.snd i (x _) } where toFun x
参数：I : MulticospanIndex J C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary equivalence to be used in `multiequalizerEquiv` below.
-/
def multiequalizerEquivAux {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :
    (I.multicospan ⋙ forget C).sections ≃
    { x : ∀ i : J.L, ToType (I.left i) // ∀ i : J.R, I.fst i (x _) = I.snd i (x _) } where
  toFun x :=
    ⟨fun _ => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      rw [← b] at a
      exact a⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left _ => x.1 _
        | WalkingMulticospan.right b => I.fst b (x.1 _)
      property := by
        rintro (a | b) (a' | b') (f | f | f)
        · simp only [WalkingMulticospan.Hom.id_eq_id, Functor.map_id]; rfl
        · rfl
        · dsimp
          exact (x.2 b').symm
        · simp only [WalkingMulticospan.Hom.id_eq_id, Functor.map_id]; rfl }
  left_inv := by
    intro x; ext (a | b)
    · rfl
    · rw [← x.2 (WalkingMulticospan.Hom.fst b)]
      rfl
  right_inv := by
    intro x
    ext i
    rfl

/-- The equivalence between the noncomputable multiequalizer and
the concrete multiequalizer. -/
/-
**CategoryTheory.Limits.Concrete.multiequalizerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Concrete`。
形式化陈述：multiequalizerEquiv {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J
 C) [HasMultiequalizer I] [PreservesLimit I.multicospan (forget C)] : ToType (mu
ltiequalizer I) ≃ { x : forall i : J.L, ToType (I.left i) // forall i : J.R, I.f
st i (x _) = I.snd i (x _) }
参数：I : MulticospanIndex J C；forget C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence between the noncomputable multiequalizer and
the concrete multiequalizer.
-/
noncomputable def multiequalizerEquiv {J : MulticospanShape.{w, w'}}
    (I : MulticospanIndex J C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] :
    ToType (multiequalizer I) ≃
      { x : ∀ i : J.L, ToType (I.left i) // ∀ i : J.R, I.fst i (x _) = I.snd i (x _) } :=
  letI h1 := limit.isLimit I.multicospan
  letI h2 := isLimitOfPreserves (forget C) h1
  (Types.isLimitEquivSections h2).trans (Concrete.multiequalizerEquivAux I)

@[simp]
/-
**CategoryTheory.Limits.Concrete.multiequalizerEquiv_apply** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：multiequalizerEquiv_apply {J : MulticospanShape.{w, w'}} (I : MulticospanI
ndex J C) [HasMultiequalizer I] [PreservesLimit I.multicospan (forget C)] (x : T
oType (multiequalizer I)) (i : J.L) : ((Concrete.multiequalizerEquiv I) x : fora
ll i : J.L, ToType (I.left i)) i = Multiequalizer.ι I i x
参数：I : MulticospanIndex J C；forget C；x : ToType (multiequalizer I)；i : J.L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multiequalizerEquiv_apply {J : MulticospanShape.{w, w'}}
    (I : MulticospanIndex J C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x : ToType (multiequalizer I)) (i : J.L) :
    ((Concrete.multiequalizerEquiv I) x : ∀ i : J.L, ToType (I.left i)) i =
      Multiequalizer.ι I i x :=
  rfl

end Multiequalizer

section WidePushout

open WidePushout

open WidePushoutShape

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC]

/-
**CategoryTheory.Limits.Concrete.widePushout_exists_rep** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.Concrete`。
形式化陈述：widePushout_exists_rep {B : C} {α : Type _} {X : α -> C} (f : forall j : α
, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget
 C)] (x : ToType (widePushout B X f)) : (exists y : ToType B, head f y = x) ∨ ex
ists (i : α) (y : ToType (X i)), ι f i y = x
参数：f : forall j : α, B ⟶ X j；wideSpan B X f；forget C；x : ToType (widePushout B X
 f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.colimit_exists_rep`：colimit_exists_rep [H
asColimit F] (x : ToType (colimit F)) : exists (j : J) (y : ToType (F.obj j)), c
olimit.ι F j y = x
-/
theorem widePushout_exists_rep {B : C} {α : Type _} {X : α → C} (f : ∀ j : α, B ⟶ X j)
    [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ToType (widePushout B X f)) :
    (∃ y : ToType B, head f y = x) ∨ ∃ (i : α) (y : ToType (X i)), ι f i y = x := by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  · left
    use y
    rfl
  · right
    use j, y
    rfl
/-
**CategoryTheory.Limits.Concrete.widePushout_exists_rep'** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.Concrete`。
形式化陈述：widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α -> C} (f 
: forall j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan 
B X f) (forget C)] (x : ToType (widePushout B X f)) : exists (i : α) (y : ToType
 (X i)), ι f i y = x
参数：f : forall j : α, B ⟶ X j；wideSpan B X f；forget C；x : ToType (widePushout B X
 f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.widePushout_exists_rep`：widePushout_exist
s_rep {B : C} {α : Type _} {X : α -> C} (f : forall j : α, B ⟶ X j) [HasWidePush
out.{v} B X f] [PreservesColimit (wideSpan …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.WidePushout.arrow_ι`：arrow_ι (j : J) : arrows j ≫ 
ι arrows j = head arrows
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α → C}
    (f : ∀ j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ToType (widePushout B X f)) : ∃ (i : α) (y : ToType (X i)), ι f i y = x := by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  · inhabit α
    use default, f _ y
    simp only [← arrow_ι _ default, ConcreteCategory.comp_apply]
  · use i, y

end WidePushout

attribute [local ext] ConcreteCategory.hom_ext in
-- We don't mark this as an `@[ext]` lemma as we don't always want to work elementwise.
/-
**CategoryTheory.Limits.Concrete.cokernel_funext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Concrete`。
形式化陈述：cokernel_funext {C : Type*} [Category* C] [HasZeroMorphisms C] {FC : C -> 
C -> Type*} {CC : C -> Type*} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [Conc
reteCategory C FC] {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K
} (w : forall n : ToType N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h
参数：FC X Y；CC X；CC Y；w : forall n : ToType N, g (cokernel.π f n) = h (cokernel.π 
f n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
theorem cokernel_funext {C : Type*} [Category* C] [HasZeroMorphisms C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K}
    (w : ∀ n : ToType N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h := by
  ext x
  simpa using w x

-- TODO: Add analogous lemmas about coproducts and coequalizers.

end CategoryTheory.Limits.Concrete

