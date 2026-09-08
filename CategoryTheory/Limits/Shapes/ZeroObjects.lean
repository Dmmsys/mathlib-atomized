/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `CategoryTheory.Limits.Shapes.ZeroMorphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace CategoryTheory

namespace Limits

/-- An object `X` in a category is a *zero object* if for every object `Y`
there is a unique morphism `to : X → Y` and a unique morphism `from : Y → X`.

This is a characteristic predicate for `HasZeroObject`. -/
/-
**CategoryTheory.Limits.IsZero** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` in a category is a *zero object* if for every object `Y`
there is a unique morphism `to : X → Y` and a unique morphism `from : Y → X`.

This is a characteristic predicate for `HasZeroObject`.
-/
structure IsZero (X : C) : Prop where
  /-- there are unique morphisms to the object -/
  unique_to : ∀ Y, Nonempty (Unique (X ⟶ Y))
  /-- there are unique morphisms from the object -/
  unique_from : ∀ Y, Nonempty (Unique (Y ⟶ X))

namespace IsZero

variable {X Y : C}

/-- If `h : IsZero X`, then `h.to_ Y` is a choice of unique morphism `X → Y`.

`to` is a reserved word, it was replaced by `to_`
-/
/-
**CategoryTheory.Limits.IsZero.to_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.IsZero`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X : C} → Categ
oryTheory.Limits.IsZero X → (Y : C) → X ⟶ Y
参数：Y : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unique_to`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C), 
Nonempty (Unique (X ⟶ Y))

--- 原说明 ---
If `h : IsZero X`, then `h.to_ Y` is a choice of unique morphism `X → Y`.

`to` is a reserved word, it was replaced by `to_`
-/
protected def to_ (h : IsZero X) (Y : C) : X ⟶ Y :=
  @default _ <| (h.unique_to Y).some.toInhabited
/-
**CategoryTheory.Limits.IsZero.eq_to** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.IsZero`。
形式化陈述：eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to_ Y
参数：h : IsZero X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `CategoryTheory.Limits.IsZero.unique_to`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C), 
Nonempty (Unique (X ⟶ Y))
-/
theorem eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to_ Y :=
  @Unique.eq_default _ (id _) _
/-
**CategoryTheory.Limits.IsZero.to_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.IsZero`。
形式化陈述：to_eq (h : IsZero X) (f : X ⟶ Y) : h.to_ Y = f
参数：h : IsZero X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_to`：eq_to (h : IsZero X) (f : X ⟶ Y) : f
 = h.to_ Y
-/
theorem to_eq (h : IsZero X) (f : X ⟶ Y) : h.to_ Y = f :=
  (h.eq_to f).symm

/-- If `h : is_zero X`, then `h.from_ Y` is a choice of unique morphism `Y → X`.

`from` is a reserved word, it was replaced by `from_`
-/
/-
**CategoryTheory.Limits.IsZero.from_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsZero`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X : C} → Categ
oryTheory.Limits.IsZero X → (Y : C) → Y ⟶ X
参数：Y : C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unique_from`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C)
, Nonempty (Unique (Y ⟶ X))

--- 原说明 ---
If `h : is_zero X`, then `h.from_ Y` is a choice of unique morphism `Y → X`.

`from` is a reserved word, it was replaced by `from_`
-/
protected def from_ (h : IsZero X) (Y : C) : Y ⟶ X :=
  @default _ <| (h.unique_from Y).some.toInhabited
/-
**CategoryTheory.Limits.IsZero.eq_from** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.IsZero`。
形式化陈述：eq_from (h : IsZero X) (f : Y ⟶ X) : f = h.from_ Y
参数：h : IsZero X；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `CategoryTheory.Limits.IsZero.unique_from`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C)
, Nonempty (Unique (Y ⟶ X))
-/
theorem eq_from (h : IsZero X) (f : Y ⟶ X) : f = h.from_ Y :=
  @Unique.eq_default _ (id _) _
/-
**CategoryTheory.Limits.IsZero.from_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.IsZero`。
形式化陈述：from_eq (h : IsZero X) (f : Y ⟶ X) : h.from_ Y = f
参数：h : IsZero X；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_from`：eq_from (h : IsZero X) (f : Y ⟶ X)
 : f = h.from_ Y
-/
theorem from_eq (h : IsZero X) (f : Y ⟶ X) : h.from_ Y = f :=
  (h.eq_from f).symm
/-
**CategoryTheory.Limits.IsZero.eq_of_src** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsZero`。
形式化陈述：eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g
参数：hX : IsZero X；f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsZero.eq_to`：eq_to (h : IsZero X) (f : X ⟶ Y) : f
 = h.to_ Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g :=
  (hX.eq_to f).trans (hX.eq_to g).symm
/-
**CategoryTheory.Limits.IsZero.eq_of_tgt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsZero`。
形式化陈述：eq_of_tgt (hX : IsZero X) (f g : Y ⟶ X) : f = g
参数：hX : IsZero X；f g : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.IsZero.eq_from`：eq_from (h : IsZero X) (f : Y ⟶ X)
 : f = h.from_ Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_tgt (hX : IsZero X) (f g : Y ⟶ X) : f = g :=
  (hX.eq_from f).trans (hX.eq_from g).symm
/-
**CategoryTheory.Limits.IsZero.epi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its.IsZero`。
形式化陈述：epi (h : IsZero X) {Y : C} (f : Y ⟶ X) : Epi f where left_cancellation _ _
 _
参数：h : IsZero X；f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma epi (h : IsZero X) {Y : C} (f : Y ⟶ X) : Epi f where
  left_cancellation _ _ _ := h.eq_of_src _ _
/-
**CategoryTheory.Limits.IsZero.mono** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Li
mits.IsZero`。
形式化陈述：mono (h : IsZero X) {Y : C} (f : X ⟶ Y) : Mono f where right_cancellation 
_ _ _
参数：h : IsZero X；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
lemma mono (h : IsZero X) {Y : C} (f : X ⟶ Y) : Mono f where
  right_cancellation _ _ _ := h.eq_of_tgt _ _

/-- Any two zero objects are isomorphic. -/
/-
**CategoryTheory.Limits.IsZero.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.IsZero`。
形式化陈述：iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where hom
参数：hX : IsZero X；hY : IsZero Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two zero objects are isomorphic.
-/
def iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where
  hom := hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _
/-
**CategoryTheory.Limits.IsZero.isIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits.IsZero`。
形式化陈述：isIso (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f
参数：hX : IsZero X；hY : IsZero Y；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma isIso (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/-- A zero object is in particular initial. -/
/-
**CategoryTheory.Limits.IsZero.isInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsZero`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
 CategoryTheory.Limits.IsZero X → CategoryTheory.Limits.IsInitial X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unique_to`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C), 
Nonempty (Unique (X ⟶ Y))

--- 原说明 ---
A zero object is in particular initial.
-/
protected def isInitial (hX : IsZero X) : IsInitial X :=
  @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some

/-- A zero object is in particular terminal. -/
/-
**CategoryTheory.Limits.IsZero.isTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.IsZero`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
 CategoryTheory.Limits.IsZero X → CategoryTheory.Limits.IsTerminal X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unique_from`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C)
, Nonempty (Unique (Y ⟶ X))

--- 原说明 ---
A zero object is in particular terminal.
-/
protected def isTerminal (hX : IsZero X) : IsTerminal X :=
  @IsTerminal.ofUnique _ _ X fun Y => (hX.unique_from Y).some

/-- The (unique) isomorphism between any initial object and the zero object. -/
/-
**CategoryTheory.Limits.IsZero.isoIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.IsZero`。
形式化陈述：isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y
参数：hX : IsZero X；hY : IsInitial Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between any initial object and the zero object.
-/
def isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y :=
  IsInitial.uniqueUpToIso hX.isInitial hY

/-- The (unique) isomorphism between any terminal object and the zero object. -/
/-
**CategoryTheory.Limits.IsZero.isoIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.IsZero`。
形式化陈述：isoIsTerminal (hX : IsZero X) (hY : IsTerminal Y) : X ≅ Y
参数：hX : IsZero X；hY : IsTerminal Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between any terminal object and the zero object.
-/
def isoIsTerminal (hX : IsZero X) (hY : IsTerminal Y) : X ≅ Y :=
  IsTerminal.uniqueUpToIso hX.isTerminal hY
/-
**CategoryTheory.Limits.IsZero.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.IsZero`。
形式化陈述：of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X
参数：hY : IsZero Y；e : X ≅ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
theorem of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt
/-
**CategoryTheory.Limits.IsZero.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts.IsZero`。
形式化陈述：op (h : IsZero X) : IsZero (Opposite.op X)
参数：h : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
theorem op (h : IsZero X) : IsZero (Opposite.op X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩
/-
**CategoryTheory.Limits.IsZero.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits.IsZero`。
形式化陈述：unop {X : Cᵒᵖ} (h : IsZero X) : IsZero (Opposite.unop X)
参数：h : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
theorem unop {X : Cᵒᵖ} (h : IsZero X) : IsZero (Opposite.unop X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

variable (Y) in
/-- A zero object is a retract of every object. -/
/-
**CategoryTheory.Limits.IsZero.retract** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsZero`。
形式化陈述：retract (h : IsZero X) : Retract X Y where i
参数：h : IsZero X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is a retract of every object.
-/
def retract (h : IsZero X) : Retract X Y where
  i := h.to_ Y
  r := h.from_ Y
  retract := h.isInitial.hom_ext _ _

end IsZero

end Limits

open CategoryTheory.Limits

/-
**CategoryTheory.Iso.isZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (e : X 
≅ Y),   CategoryTheory.Limits.IsZero X ↔ CategoryTheory.Limits.IsZero Y
参数：e : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
theorem Iso.isZero_iff {X Y : C} (e : X ≅ Y) : IsZero X ↔ IsZero Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩
/-
**CategoryTheory.Functor.isZero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.Functor C D), (
∀ (X : C), CategoryTheory.Limits.IsZero (F.obj X)) → CategoryTheory.Limits.IsZer
o F
参数：F : CategoryTheory.Functor C D；∀ (X : C), CategoryTheory.Limits.IsZero (F.obj
 X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
theorem Functor.isZero (F : C ⥤ D) (hF : ∀ X, IsZero (F.obj X)) : IsZero F := by
  constructor <;> intro G <;> refine ⟨⟨⟨?_⟩, ?_⟩⟩
  · refine
      { app := fun X => (hF _).to_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_src _ _
  · intro f
    ext
    apply (hF _).eq_of_src _ _
  · refine
      { app := fun X => (hF _).from_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_tgt _ _
  · intro f
    ext
    apply (hF _).eq_of_tgt _ _

namespace Limits

variable (C)

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
/-
**CategoryTheory.Limits.HasZeroObject** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category "has a zero object" if it has an object which is both initial and ter
minal.
-/
class HasZeroObject : Prop where
  /-- there exists a zero object -/
  zero : ∃ X : C, IsZero X
/-
**CategoryTheory.Limits.hasZeroObject_pUnit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：hasZeroObject_pUnit : HasZeroObject (Discrete PUnit) where zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance hasZeroObject_pUnit : HasZeroObject (Discrete PUnit) where zero :=
  ⟨⟨⟨⟩⟩,
    { unique_to := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩
      unique_from := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩}⟩

section

variable [HasZeroObject C]

/-- Construct a `Zero C` for a category with a zero object.
This cannot be a global instance as it will trigger for every `Zero C` typeclass search.
-/
@[instance_reducible]
/-
**CategoryTheory.Limits.HasZeroObject.zero'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.HasZeroObject`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasZeroObject C] → Zero C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.zero`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroObject C],   ∃ X
, CategoryTheory.Limits.IsZero…

--- 原说明 ---
Construct a `Zero C` for a category with a zero object.
This cannot be a global instance as it will trigger for every `Zero C` typeclass
 search.
-/
protected def HasZeroObject.zero' : Zero C where zero := HasZeroObject.zero.choose

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

open ZeroObject
/-
**CategoryTheory.Limits.isZero_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：isZero_zero : IsZero (0 : C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Limits.HasZeroObject.zero`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroObject C],   ∃ X
, CategoryTheory.Limits.IsZero…
-/
theorem isZero_zero : IsZero (0 : C) :=
  HasZeroObject.zero.choose_spec
/-
**CategoryTheory.Limits.hasZeroObject_op** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：hasZeroObject_op : HasZeroObject Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.op`：op (h : IsZero X) : IsZero (Opposite.op
 X)
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
instance hasZeroObject_op : HasZeroObject Cᵒᵖ :=
  ⟨⟨Opposite.op 0, IsZero.op (isZero_zero C)⟩⟩

end

open ZeroObject

/-
**CategoryTheory.Limits.hasZeroObject_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：hasZeroObject_unop [HasZeroObject Cᵒᵖ] : HasZeroObject C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unop`：unop {X : Cᵒᵖ} (h : IsZero X) : IsZer
o (Opposite.unop X)
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
theorem hasZeroObject_unop [HasZeroObject Cᵒᵖ] : HasZeroObject C :=
  ⟨⟨Opposite.unop 0, IsZero.unop (isZero_zero Cᵒᵖ)⟩⟩

variable {C}
/-
**CategoryTheory.Limits.IsZero.hasZeroObject** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C},   Catego
ryTheory.Limits.IsZero X → CategoryTheory.Limits.HasZeroObject C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsZero.hasZeroObject {X : C} (hX : IsZero X) : HasZeroObject C :=
  ⟨⟨X, hX⟩⟩

/-- Every zero object is isomorphic to *the* zero object. -/
/-
**CategoryTheory.Limits.IsZero.isoZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsZero`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] → {X : C} → CategoryTheory.Limits.IsZero
 X → (X ≅ 0)
参数：X ≅ 0。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
Every zero object is isomorphic to *the* zero object.
-/
def IsZero.isoZero [HasZeroObject C] {X : C} (hX : IsZero X) : X ≅ 0 :=
  hX.iso (isZero_zero C)
/-
**CategoryTheory.Limits.IsZero.obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   [CategoryTheory.Limits.HasZeroObjec
t D] {F : CategoryTheory.Functor C D},   CategoryTheory.Limits.IsZero F → ∀ (X :
 C), CategoryTheory.Limits.IsZero (F.obj X)
参数：X : C；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isZero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (F
 : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
theorem IsZero.obj [HasZeroObject D] {F : C ⥤ D} (hF : IsZero F) (X : C) : IsZero (F.obj X) := by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : IsZero G := Functor.isZero _ fun _ => isZero_zero _
  let e : F ≅ G := hF.iso hG
  exact (isZero_zero _).of_iso (e.app X)
/-
**CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.Functor C D) [F
.Full] [F.Faithful] (X : C),   CategoryTheory.Limits.IsZero (F.obj X) → Category
Theory.Limits.IsZero X
参数：F : CategoryTheory.Functor C D；X : C；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unique_to`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C), 
Nonempty (Unique (X ⟶ Y))
· 使用定理 `CategoryTheory.Limits.IsZero.unique_from`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X : C},   CategoryTheory.Limits.IsZero X → ∀ (Y : C)
, Nonempty (Unique (Y ⟶ X))
-/
lemma IsZero.of_full_of_faithful_of_isZero
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) (hX : IsZero (F.obj X)) :
    IsZero X := by
  have h : F.FullyFaithful := .ofFullyFaithful _
  have (Y : C) := (hX.unique_to (F.obj Y)).some
  have (Y : C) := (hX.unique_from (F.obj Y)).some
  exact ⟨fun Y ↦ ⟨h.homEquiv.unique⟩, fun Y ↦ ⟨h.homEquiv.unique⟩⟩

namespace HasZeroObject

variable [HasZeroObject C]

/-- There is a unique morphism from the zero object to any object `X`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.HasZeroObject.uniqueTo** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.HasZeroObject`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] → (X : C) → Unique (0 ⟶ X)
参数：X : C；0 ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique morphism from the zero object to any object `X`.
-/
protected def uniqueTo (X : C) : Unique (0 ⟶ X) :=
  ((isZero_zero C).unique_to X).some

/-- There is a unique morphism from any object `X` to the zero object. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.HasZeroObject.uniqueFrom** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.HasZeroObject`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] → (X : C) → Unique (X ⟶ 0)
参数：X : C；X ⟶ 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique morphism from any object `X` to the zero object.
-/
protected def uniqueFrom (X : C) : Unique (X ⟶ 0) :=
  ((isZero_zero C).unique_from X).some

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]
/-
**CategoryTheory.Limits.HasZeroObject.to_zero_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.HasZeroObject`。
形式化陈述：to_zero_ext {X : C} (f g : X ⟶ 0) : f = g
参数：f g : X ⟶ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
theorem to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
  (isZero_zero C).eq_of_tgt _ _

@[ext]
/-
**CategoryTheory.Limits.HasZeroObject.from_zero_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.HasZeroObject`。
形式化陈述：from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g
参数：f g : 0 ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
theorem from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g :=
  (isZero_zero C).eq_of_src _ _
/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Subsingleton (X ≅ 0) := ⟨fun f g => by ext⟩
/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : 0 ⟶ X) : Mono f where right_cancellation g h _ := by ext
/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : X ⟶ 0) : Epi f where left_cancellation g h _ := by ext
/-
**CategoryTheory.Limits.HasZeroObject.zero_to_zero_isIso** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zero_to_zero_isIso (f : (0 : C) ⟶ 0) : IsIso f
参数：f : (0 : C) ⟶ 0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
instance zero_to_zero_isIso (f : (0 : C) ⟶ 0) : IsIso f := by
  convert! show IsIso (𝟙 (0 : C)) by infer_instance
  subsingleton

/-- A zero object is in particular initial. -/
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsInitial : IsInitial (0 : C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
A zero object is in particular initial.
-/
def zeroIsInitial : IsInitial (0 : C) :=
  (isZero_zero C).isInitial

/-- A zero object is in particular terminal. -/
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsTerminal : IsTerminal (0 : C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
A zero object is in particular terminal.
-/
def zeroIsTerminal : IsTerminal (0 : C) :=
  (isZero_zero C).isTerminal

/-- A zero object is in particular initial. -/
/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is in particular initial.
-/
instance (priority := 10) hasInitial : HasInitial C :=
  hasInitial_of_unique 0

/-- A zero object is in particular terminal. -/
/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is in particular terminal.
-/
instance (priority := 10) hasTerminal : HasTerminal C :=
  hasTerminal_of_unique 0

/-- The (unique) isomorphism between any initial object and the zero object. -/
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoIsInitial {X : C} (t : IsInitial X) : 0 ≅ X
参数：t : IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between any initial object and the zero object.
-/
def zeroIsoIsInitial {X : C} (t : IsInitial X) : 0 ≅ X :=
  zeroIsInitial.uniqueUpToIso t

/-- The (unique) isomorphism between any terminal object and the zero object. -/
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoIsTerminal {X : C} (t : IsTerminal X) : 0 ≅ X
参数：t : IsTerminal X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between any terminal object and the zero object.
-/
def zeroIsoIsTerminal {X : C} (t : IsTerminal X) : 0 ≅ X :=
  zeroIsTerminal.uniqueUpToIso t

/-- The (unique) isomorphism between the chosen initial object and the chosen zero object. -/
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoInitial** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoInitial [HasInitial C] : 0 ≅ ⊥_ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between the chosen initial object and the chosen zero o
bject.
-/
def zeroIsoInitial [HasInitial C] : 0 ≅ ⊥_ C :=
  zeroIsInitial.uniqueUpToIso initialIsInitial

/-- The (unique) isomorphism between the chosen terminal object and the chosen zero object. -/
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoTerminal [HasTerminal C] : 0 ≅ ⊤_ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between the chosen terminal object and the chosen zero 
object.
-/
def zeroIsoTerminal [HasTerminal C] : 0 ≅ ⊤_ C :=
  zeroIsTerminal.uniqueUpToIso terminalIsTerminal
/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) initialMonoClass : InitialMonoClass C :=
  InitialMonoClass.of_isInitial zeroIsInitial fun X => by infer_instance

end HasZeroObject

end Limits

open CategoryTheory.Limits

open ZeroObject

/-
**CategoryTheory.Functor.isZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   [CategoryTheory.Limits.HasZeroObjec
t D] (F : CategoryTheory.Functor C D),   CategoryTheory.Limits.IsZero F ↔ ∀ (X :
 C), CategoryTheory.Limits.IsZero (F.obj X)
参数：F : CategoryTheory.Functor C D；X : C；F.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.obj`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]  
 [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Functor.isZero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]   (F
 : CategoryTheory.F…
-/
theorem Functor.isZero_iff [HasZeroObject D] (F : C ⥤ D) : IsZero F ↔ ∀ X, IsZero (F.obj X) :=
  ⟨fun hF X => hF.obj X, Functor.isZero _⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [Category* C] (A : C) [HasZeroObject C] : Epi (terminalIsTerminal.from A) :=
  (((isZero_zero C).of_iso HasZeroObject.zeroIsoTerminal.symm).epi _)

end CategoryTheory

