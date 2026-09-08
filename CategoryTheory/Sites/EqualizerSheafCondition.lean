/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Tactic.ApplyFun

/-!
# The equalizer diagram sheaf condition for a presieve

In `Mathlib/CategoryTheory/Sites/IsSheafFor.lean` it is defined what it means for a presheaf to be a
sheaf *for* a particular presieve. In this file we provide equivalent conditions in terms of
equalizer diagrams.

* In `Equalizer.Presieve.sheaf_condition`, the sheaf condition at a presieve is shown to be
  equivalent to that of https://stacks.math.columbia.edu/tag/00VM (and combined with
  `isSheaf_pretopology`, this shows the notions of `IsSheaf` are exactly equivalent.)

* In `Equalizer.Sieve.equalizer_sheaf_condition`, the sheaf condition at a sieve is shown to be
  equivalent to that of Equation (3) p. 122 in Maclane-Moerdijk [MM92].

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)

-/

@[expose] public section


universe t w v u

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Equalizer

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type (max v u)) {X : C} (R : Presieve X)
  (S : Sieve X)

noncomputable section

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of the Stacks entry.
-/
@[stacks 00VM "This is the middle object of the fork diagram there."]
/-
**CategoryTheory.Equalizer.FirstObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Equalizer`。
形式化陈述：FirstObj : Type (max v u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The middle object of the fork diagram given in Equation (3) of [MM92], as well a
s the fork diagram
of the Stacks entry.
-/
abbrev FirstObj : Type (max v u) :=
  ∏ᶜ fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)

variable {P R}

@[ext]
/-
**CategoryTheory.Equalizer.FirstObj.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Equalizer.FirstObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.Functor Cᵒᵖ (Type (max v u))} {X : C}   {R : CategoryTheory.Presieve X} (z₁ z
₂ : CategoryTheory.Equalizer.FirstObj P R),   (∀ (Y : C) (f : Y ⟶ X) (hf : R f),
       (CategoryTheory.ConcreteCategory.hom             (CategoryTheory.Limits.P
i.π (fun f => P.obj (Opposite.op f.fst)) ⟨Y, ⟨f, hf⟩⟩))           z₁ =         (
CategoryTheory.ConcreteCategory.hom             (CategoryTheory.Limits.Pi.π (fun
 f => P.obj (Opposite.op f.fst)) ⟨Y, ⟨f, hf⟩⟩))           z₂) →     z₁ = z₂
参数：Type (max v u)；z₁ z₂ : CategoryTheory.Equalizer.FirstObj P R；∀ (Y : C) (f : Y
 ⟶ X) (hf : R f),       (CategoryTheory.ConcreteCategory.hom             (Catego
ryTheory.Limits.Pi.π (fun f => P.obj (Opposite.op f.fst)) ⟨Y, ⟨f, hf⟩⟩))        
   z₁ =         (CategoryTheory.ConcreteCategory.hom             (CategoryTheory
.Limits.Pi.π (fun f => P.obj (Opposite.op f.fst)) ⟨Y, ⟨f, hf⟩⟩))           z₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
-/
lemma FirstObj.ext (z₁ z₂ : FirstObj P R) (h : ∀ (Y : C) (f : Y ⟶ X)
    (hf : R f), (Pi.π _ ⟨Y, f, hf⟩ : FirstObj P R ⟶ _) z₁ =
      (Pi.π _ ⟨Y, f, hf⟩ : FirstObj P R ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, f, hf⟩⟩
  exact h Y f hf

variable (P R)

set_option backward.isDefEq.respectTransparency.types false in
/-- Show that `FirstObj` is isomorphic to `FamilyOfElements`. -/
@[simps]
/-
**CategoryTheory.Equalizer.firstObjEqFamily** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Equalizer`。
形式化陈述：firstObjEqFamily : FirstObj P R ≅ (R.FamilyOfElements P) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that `FirstObj` is isomorphic to `FamilyOfElements`.
-/
def firstObjEqFamily : FirstObj P R ≅ (R.FamilyOfElements P) where
  hom := ↾fun t _ _ hf ↦
    Pi.π (fun f : Σ Y, { f : Y ⟶ X // R f } => P.obj (op f.1)) ⟨_, _, hf⟩ t
  inv := Pi.lift fun f => ↾fun x => x _ f.2.2
/-
**CategoryTheory.Equalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equalizer`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FirstObj P (⊥ : Presieve X)) :=
  (firstObjEqFamily P _).toEquiv.inhabited
/-
**CategoryTheory.Equalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equalizer`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FirstObj P ((⊥ : Sieve X) : Presieve X)) :=
  inferInstanceAs <| Inhabited (FirstObj P (⊥ : Presieve X))

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of the Stacks entry.
-/
@[stacks 00VM "This is the left morphism of the fork diagram there."]
/-
**CategoryTheory.Equalizer.forkMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equ
alizer`。
形式化陈述：forkMap : P.obj (op X) ⟶ FirstObj P R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left morphism of the fork diagram given in Equation (3) of [MM92], as well a
s the fork diagram
of the Stacks entry.
-/
def forkMap : P.obj (op X) ⟶ FirstObj P R :=
  Pi.lift fun f => P.map f.2.1.op

/-!
This section establishes the equivalence between the sheaf condition of Equation (3) [MM92] and
the definition of `IsSheafFor`.
-/


namespace Sieve

/-- The rightmost object of the fork diagram of Equation (3) [MM92], which contains the data used
to check a family is compatible.
-/
/-
**CategoryTheory.Equalizer.Sieve.SecondObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Equalizer.Sieve`。
形式化陈述：SecondObj : Type (max v u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rightmost object of the fork diagram of Equation (3) [MM92], which contains 
the data used
to check a family is compatible.
-/
abbrev SecondObj : Type (max v u) :=
  ∏ᶜ fun f : Σ (Y Z : _) (_ : Z ⟶ Y), { f' : Y ⟶ X // S f' } => P.obj (op f.2.1)

variable {P S}

@[ext]
/-
**CategoryTheory.Equalizer.Sieve.SecondObj.ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Equalizer.Sieve.SecondObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.Functor Cᵒᵖ (Type (max v u))} {X : C}   {S : CategoryTheory.Sieve X} (z₁ z₂ :
 CategoryTheory.Equalizer.Sieve.SecondObj P S),   (∀ (Y Z : C) (g : Z ⟶ Y) (f : 
Y ⟶ X) (hf : S.arrows f),       (CategoryTheory.ConcreteCategory.hom            
 (CategoryTheory.Limits.Pi.π (fun f => P.obj (Opposite.op f.snd.fst)) ⟨Y, ⟨Z, ⟨g
, ⟨f, hf⟩⟩⟩⟩))           z₁ =         (CategoryTheory.ConcreteCategory.hom      
       (CategoryTheory.Limits.Pi.π (fun f => P.obj (Opposite.op f.snd.fst)) ⟨Y, 
⟨Z, ⟨g, ⟨f, hf⟩⟩⟩⟩))           z₂) →     z₁ = z₂
参数：Type (max v u)；z₁ z₂ : CategoryTheory.Equalizer.Sieve.SecondObj P S；∀ (Y Z : 
C) (g : Z ⟶ Y) (f : Y ⟶ X) (hf : S.arrows f),       (CategoryTheory.ConcreteCate
gory.hom             (CategoryTheory.Limits.Pi.π (fun f => P.obj (Opposite.op f.
snd.fst)) ⟨Y, ⟨Z, ⟨g, ⟨f, hf⟩⟩⟩⟩))           z₁ =         (CategoryTheory.Concre
teCategory.hom             (CategoryTheory.Limits.Pi.π (fun f => P.obj (Opposite
.op f.snd.fst)) ⟨Y, ⟨Z, ⟨g, ⟨f, hf⟩⟩⟩⟩))           z₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
-/
lemma SecondObj.ext (z₁ z₂ : SecondObj P S) (h : ∀ (Y Z : C) (g : Z ⟶ Y) (f : Y ⟶ X)
    (hf : S.arrows f), (Pi.π _ ⟨Y, Z, g, f, hf⟩ : SecondObj P S ⟶ _) z₁ =
      (Pi.π _ ⟨Y, Z, g, f, hf⟩ : SecondObj P S ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨⟨Y, Z, g, f, hf⟩⟩
  apply h

variable (P S)

/-- The map `p` of Equations (3,4) [MM92]. -/
/-
**CategoryTheory.Equalizer.Sieve.firstMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Equalizer.Sieve`。
形式化陈述：firstMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `p` of Equations (3,4) [MM92].
-/
def firstMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg =>
    Pi.π _ (⟨_, _, S.downward_closed fg.2.2.2.2 fg.2.2.1⟩ : Σ Y, { f : Y ⟶ X // S f })
/-
**CategoryTheory.Equalizer.Sieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equa
lizer.Sieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SecondObj P (⊥ : Sieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `a` of Equations (3,4) [MM92]. -/
/-
**CategoryTheory.Equalizer.Sieve.secondMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equalizer.Sieve`。
形式化陈述：secondMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `a` of Equations (3,4) [MM92].
-/
def secondMap : FirstObj P (S : Presieve X) ⟶ SecondObj P S :=
  Pi.lift fun fg => Pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map fg.2.2.1.op
/-
**CategoryTheory.Equalizer.Sieve.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Equ
alizer.Sieve`。
形式化陈述：w : forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P 
S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem w : forkMap P (S : Presieve X) ≫ firstMap P S = forkMap P S ≫ secondMap P S := by
  ext
  simp [firstMap, secondMap, forkMap]

set_option backward.isDefEq.respectTransparency false in
/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
-/
/-
**CategoryTheory.Equalizer.Sieve.compatible_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Equalizer.Sieve`。
形式化陈述：compatible_iff (x : FirstObj P S.arrows) : ((firstObjEqFamily P S.arrows).
hom x).Compatible ↔ firstMap P S x = secondMap P S x
参数：x : FirstObj P S.arrows。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.compatible_iff_sieveCompatible`：compatible_iff_s
ieveCompatible (x : FamilyOfElements P (S : Presieve X)) : x.Compatible ↔ x.Siev
eCompatible
· 使用定理 `CategoryTheory.Equalizer.Sieve.SecondObj.ext`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))}
 {X : C}   {S : CategoryTheory.Sie…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Equalizer.firstObjEqFamily_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))
) {X : C}   (R : CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Limits.Types.limit_ext_iff'`：limit_ext_iff' (F' : J ⥤ Typ
e v) (x y : limit F') : x = y ↔ forall j, limit.π F' j x = limit.π F' j y

--- 原说明 ---
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` 
and `secondMap`
map it to the same point.
-/
theorem compatible_iff (x : FirstObj P S.arrows) :
    ((firstObjEqFamily P S.arrows).hom x).Compatible ↔ firstMap P S x = secondMap P S x := by
  rw [Presieve.compatible_iff_sieveCompatible]
  constructor
  · intro t
    apply SecondObj.ext
    intro Y Z g f hf
    simpa [firstMap, secondMap] using t _ g hf
  · intro t Y Z f g hf
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨Y, Z, g, f, hf⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- `P` is a sheaf for `S`, iff the fork given by `w` is an equalizer. -/
/-
**CategoryTheory.Equalizer.Sieve.equalizer_sheaf_condition** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Equalizer.Sieve`。
形式化陈述：equalizer_sheaf_condition : Presieve.IsSheafFor P (S : Presieve X) ↔ Nonem
pty (IsLimit (Fork.ofι _ (w P S)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equalizer.Sieve.w`：w : forkMap P (S : Presieve X) ≫ first
Map P S = forkMap P S ≫ secondMap P S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.toEquiv_symm_apply`：∀ {X Y : Type u} (i : X ≅ Y) (a :
 Y), i.toEquiv.symm a = (CategoryTheory.ConcreteCategory.hom i.inv) a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `existsUnique_congr`：existsUnique_congr {p q : α -> Prop} (h : forall a, 
p a ↔ q a) : (exists! a, p a) ↔ exists! a, q a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.ext`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X :
 C}   {R : CategoryTheory.Presieve…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equalizer.firstObjEqFamily_inv`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))
) {X : C}   (R : CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Equalizer.firstObjEqFamily_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))
) {X : C}   (R : CategoryTheory.Pre…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`P` is a sheaf for `S`, iff the fork given by `w` is an equalizer.
-/
theorem equalizer_sheaf_condition :
    Presieve.IsSheafFor P (S : Presieve X) ↔ Nonempty (IsLimit (Fork.ofι _ (w P S))) := by
  rw [Types.type_equalizer_iff_unique,
    ← Equiv.forall_congr_right (firstObjEqFamily P (S : Presieve X)).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1, 2]; rw [(firstObjEqFamily P S.arrows).toEquiv_symm_apply]
  simp only [Iso.inv_hom_id_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    ext Y f hf
    simpa [Iso.toEquiv, forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [Iso.toEquiv, forkMap]

end Sieve

/-!
This section establishes the equivalence between the sheaf condition of
https://stacks.math.columbia.edu/tag/00VM and the definition of `isSheafFor`.
-/


namespace Presieve

variable [R.HasPairwisePullbacks]

/--
The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[simp, stacks 00VM "This is the rightmost object of the fork diagram there."]
/-
**CategoryTheory.Equalizer.Presieve.SecondObj** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equalizer.Presieve`。
形式化陈述：SecondObj : Type (max v u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatibl
e.
-/
def SecondObj : Type (max v u) :=
  ∏ᶜ fun fg : (Σ Y, { f : Y ⟶ X // R f }) × Σ Z, { g : Z ⟶ X // R g } =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "This is the map `pr₀*` there."]
/-
**CategoryTheory.Equalizer.Presieve.firstMap** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Equalizer.Presieve`。
形式化陈述：firstMap : FirstObj P R ⟶ SecondObj P R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `pr₀*` of the Stacks entry.
-/
def firstMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.fst _ _).op
/-
**CategoryTheory.Equalizer.Presieve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.E
qualizer.Presieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPullbacks C] : Inhabited (SecondObj P (⊥ : Presieve X)) :=
  ⟨firstMap _ _ default⟩

/-- The map `pr₁*` of the Stacks entry. -/
@[stacks 00VM "This is the map `pr₁*` there."]
/-
**CategoryTheory.Equalizer.Presieve.secondMap** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equalizer.Presieve`。
形式化陈述：secondMap : FirstObj P R ⟶ SecondObj P R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `pr₁*` of the Stacks entry.
-/
def secondMap : FirstObj P R ⟶ SecondObj P R :=
  Pi.lift fun fg =>
    haveI := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
    Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Equalizer.Presieve.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Equalizer.Presieve`。
形式化陈述：w : forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `CategoryTheory.Presieve.HasPairwisePullbacks.has_pullbacks`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Pres
ieve X}   [self : R.HasPairwisePullbacks] {Y Z :…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
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
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem w : forkMap P R ≫ firstMap P R = forkMap P R ≫ secondMap P R := by
  dsimp
  ext fg
  simp only [firstMap, secondMap, forkMap]
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app]
  have := Presieve.HasPairwisePullbacks.has_pullbacks fg.1.2.2 fg.2.2.2
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
-/
/-
**CategoryTheory.Equalizer.Presieve.compatible_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equalizer.Presieve`。
形式化陈述：compatible_iff (x : FirstObj P R) : ((firstObjEqFamily P R).hom x).Compati
ble ↔ firstMap P R x = secondMap P R x
参数：x : FirstObj P R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.pullbackCompatible_iff`：pullbackCompatible_iff (
x : FamilyOfElements P R) [R.HasPairwisePullbacks] : x.Compatible ↔ x.PullbackCo
mpatible
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Presieve.HasPairwisePullbacks.has_pullbacks`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Pres
ieve X}   [self : R.HasPairwisePullbacks] {Y Z :…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Equalizer.firstObjEqFamily_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))
) {X : C}   (R : CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Limits.Types.limit_ext_iff'`：limit_ext_iff' (F' : J ⥤ Typ
e v) (x y : limit F') : x = y ↔ forall j, limit.π F' j x = limit.π F' j y

--- 原说明 ---
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` 
and `secondMap`
map it to the same point.
-/
theorem compatible_iff (x : FirstObj P R) :
    ((firstObjEqFamily P R).hom x).Compatible ↔ firstMap P R x = secondMap P R x := by
  rw [Presieve.pullbackCompatible_iff]
  constructor
  · intro t
    apply Limits.Types.limit_ext
    rintro ⟨⟨Y, f, hf⟩, Z, g, hg⟩
    simpa [firstMap, secondMap] using t hf hg
  · intro t Y Z f g hf hg
    rw [Types.limit_ext_iff'] at t
    simpa [firstMap, secondMap] using t ⟨⟨⟨Y, f, hf⟩, Z, g, hg⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- `P` is a sheaf for `R`, iff the fork given by `w` is an equalizer. -/
@[stacks 00VM]
/-
**CategoryTheory.Equalizer.Presieve.sheaf_condition** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Equalizer.Presieve`。
形式化陈述：sheaf_condition : R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equalizer.Presieve.w`：w : forkMap P R ≫ firstMap P R = fo
rkMap P R ≫ secondMap P R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.toEquiv_apply`：∀ {X Y : Type u} (i : X ≅ Y) (a : X), 
i.toEquiv a = (CategoryTheory.ConcreteCategory.hom i.hom) a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `existsUnique_congr`：existsUnique_congr {p q : α -> Prop} (h : forall a, 
p a ↔ q a) : (exists! a, p a) ↔ exists! a, q a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equalizer.firstObjEqFamily_inv`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))
) {X : C}   (R : CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Equalizer.firstObjEqFamily_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type (max v u))
) {X : C}   (R : CategoryTheory.Pre…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`P` is a sheaf for `R`, iff the fork given by `w` is an equalizer.
-/
theorem sheaf_condition : R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (w P R))) := by
  rw [Types.type_equalizer_iff_unique,
    ← Equiv.forall_congr_right (firstObjEqFamily P R).toEquiv.symm]
  simp_rw [← compatible_iff]
  conv => enter [2, a, 1, 1]; rw [← Iso.toEquiv_apply]
  simp_rw [Equiv.apply_symm_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply]
  constructor
  · intro q
    funext Y f hf
    simpa [Iso.toEquiv, forkMap] using q _ _
  · intro q Y f hf
    rw [← q]
    simp [Iso.toEquiv, forkMap]

namespace Arrows

variable (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Presieve X) (S : Sieve X)

open Presieve

variable {B : C} {I : Type t} [Small.{w} I] (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks]

/--
The middle object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.FirstObj P (ofArrows X π)` arises if the family of
arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
@[stacks 00VM "The middle object of the fork diagram there."]
/-
**CategoryTheory.Equalizer.Presieve.Arrows.FirstObj** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：FirstObj : Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The middle object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.FirstObj P (ofArrows X π)` arises if 
the family of
arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
abbrev FirstObj : Type w := ∏ᶜ (fun i ↦ P.obj (op (X i)))

@[ext]
/-
**CategoryTheory.Equalizer.Presieve.Arrows.FirstObj.ext** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Equalizer.Presieve.Arrows.FirstObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.Functor Cᵒᵖ (Type w)) {I : Type t}   [inst_1 : Small.{w, t} I] (X : I → C) (z
₁ z₂ : CategoryTheory.Equalizer.Presieve.Arrows.FirstObj P X),   (∀ (i : I),    
   (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.Pi.π (fun i => P.
obj (Opposite.op (X i))) i)) z₁ =         (CategoryTheory.ConcreteCategory.hom (
CategoryTheory.Limits.Pi.π (fun i => P.obj (Opposite.op (X i))) i)) z₂) →     z₁
 = z₂
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；X : I → C；z₁ z₂ : CategoryTheory.Equa
lizer.Presieve.Arrows.FirstObj P X；∀ (i : I),       (CategoryTheory.ConcreteCate
gory.hom (CategoryTheory.Limits.Pi.π (fun i => P.obj (Opposite.op (X i))) i)) z₁
 =         (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.Pi.π (fun
 i => P.obj (Opposite.op (X i))) i)) z₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
-/
lemma FirstObj.ext (z₁ z₂ : FirstObj P X) (h : ∀ i, (Pi.π _ i : FirstObj P X ⟶ _) z₁ =
    (Pi.π _ i : FirstObj P X ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
The rightmost object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.Presieve.SecondObj P (ofArrows X π)` arises if the
family of arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see those.
-/
@[stacks 00VM "The rightmost object of the fork diagram there."]
/-
**CategoryTheory.Equalizer.Presieve.Arrows.SecondObj** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：SecondObj : Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rightmost object of the fork diagram of the Stacks entry.
The difference between this and `Equalizer.Presieve.SecondObj P (ofArrows X π)` 
arises if the
family of arrows `π` contains duplicates. The `Presieve.ofArrows` doesn't see th
ose.
-/
abbrev SecondObj : Type w :=
  ∏ᶜ (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2))))

@[ext]
/-
**CategoryTheory.Equalizer.Presieve.Arrows.SecondObj.ext** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Equalizer.Presieve.Arrows.SecondObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.Functor Cᵒᵖ (Type w)) {B : C} {I : Type t}   [inst_1 : Small.{w, t} I] (X : I
 → C) (π : (i : I) → X i ⟶ B)   [inst_2 : (CategoryTheory.Presieve.ofArrows X π)
.HasPairwisePullbacks]   (z₁ z₂ : CategoryTheory.Equalizer.Presieve.Arrows.Secon
dObj P X π),   (∀ (ij : I × I),       (CategoryTheory.ConcreteCategory.hom      
       (CategoryTheory.Limits.Pi.π               (fun ij => P.obj (Opposite.op (
CategoryTheory.Limits.pullback (π ij.1) (π ij.2)))) ij))           z₁ =         
(CategoryTheory.ConcreteCategory.hom             (CategoryTheory.Limits.Pi.π    
           (fun ij => P.obj (Opposite.op (CategoryTheory.Limits.pullback (π ij.1
) (π ij.2)))) ij))           z₂) →     z₁ = z₂
参数：P : CategoryTheory.Functor Cᵒᵖ (Type w)；X : I → C；π : (i : I) → X i ⟶ B；Categ
oryTheory.Presieve.ofArrows X π；z₁ z₂ : CategoryTheory.Equalizer.Presieve.Arrows
.SecondObj P X π；∀ (ij : I × I),       (CategoryTheory.ConcreteCategory.hom     
        (CategoryTheory.Limits.Pi.π               (fun ij => P.obj (Opposite.op 
(CategoryTheory.Limits.pullback (π ij.1) (π ij.2)))) ij))           z₁ =        
 (CategoryTheory.ConcreteCategory.hom             (CategoryTheory.Limits.Pi.π   
            (fun ij => P.obj (Opposite.op (CategoryTheory.Limits.pullback (π ij.
1) (π ij.2)))) ij))           z₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
-/
lemma SecondObj.ext (z₁ z₂ : SecondObj P X π) (h : ∀ ij, (Pi.π _ ij : SecondObj P X π ⟶ _) z₁ =
    (Pi.π _ ij : SecondObj P X π ⟶ _) z₂) : z₁ = z₂ := by
  apply Limits.Types.limit_ext
  rintro ⟨i⟩
  exact h i

/--
The left morphism of the fork diagram.
-/
/-
**CategoryTheory.Equalizer.Presieve.Arrows.forkMap** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：forkMap : P.obj (op B) ⟶ FirstObj P X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left morphism of the fork diagram.
-/
def forkMap : P.obj (op B) ⟶ FirstObj P X := Pi.lift (fun i ↦ P.map (π i).op)

/--
The first of the two parallel morphisms of the fork diagram, induced by the first projection in
each pullback.
-/
/-
**CategoryTheory.Equalizer.Presieve.Arrows.firstMap** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：firstMap : FirstObj P X ⟶ SecondObj P X π
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first of the two parallel morphisms of the fork diagram, induced by the firs
t projection in
each pullback.
-/
def firstMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/--
The second of the two parallel morphisms of the fork diagram, induced by the second projection in
each pullback.
-/
/-
**CategoryTheory.Equalizer.Presieve.Arrows.secondMap** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：secondMap : FirstObj P X ⟶ SecondObj P X π
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second of the two parallel morphisms of the fork diagram, induced by the sec
ond projection in
each pullback.
-/
def secondMap : FirstObj P X ⟶ SecondObj P X π :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Equalizer.Presieve.Arrows.w** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Equalizer.Presieve.Arrows`。
形式化陈述：w : forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem w : forkMap P X π ≫ firstMap P X π = forkMap P X π ≫ secondMap P X π := by
  ext x ij
  dsimp [forkMap, firstMap, secondMap]
  simp [← comp_apply, -types_comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition]

/--
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` and `secondMap`
map it to the same point.
See `CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff_of_small` for a version with
less universe assumptions.
-/
/-
**CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：compatible_iff {I : Type w} (X : I -> C) (π : (i : I) -> X i ⟶ B) [(Presie
ve.ofArrows X π).HasPairwisePullbacks] (x : FirstObj P X) : (Arrows.Compatible P
 π ((Types.productIso _).hom x)) ↔ firstMap P X π x = secondMap P X π x
参数：X : I -> C；π : (i : I) -> X i ⟶ B；Presieve.ofArrows X π；x : FirstObj P X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.Arrows.pullbackCompatible_iff`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryTheory.Functor Cᵒᵖ (Type
 w)) {B : C}   {I : Type u_1} {X : I → C} (…
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.SecondObj.ext`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type w
)) {B : C} {I : Type t}   [inst_1 : Small.{w…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Limits.Types.productIso_hom_comp_eval_apply`：∀ {J : Type 
v} (F : J → Type (max v u)) (j : J) (x : ∏ᶜ F),   (CategoryTheory.ConcreteCatego
ry.hom (CategoryTheory.Limits.Types.productIso F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The family of elements given by `x : FirstObj P S` is compatible iff `firstMap` 
and `secondMap`
map it to the same point.
See `CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff_of_small` for a ver
sion with
less universe assumptions.
-/
theorem compatible_iff {I : Type w} (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks] (x : FirstObj P X) :
    (Arrows.Compatible P π ((Types.productIso _).hom x)) ↔
      firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  constructor
  · intro t
    ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · intro t i j
    apply_fun Pi.π (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

/-- Version of `CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff` for a small
indexing type. -/
/-
**CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff_of_small** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：compatible_iff_of_small (x : FirstObj P X) : (Arrows.Compatible P π ((equi
vShrink _).symm ((Types.Small.productIso _).hom x))) ↔ firstMap P X π x = second
Map P X π x
参数：x : FirstObj P X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.Arrows.pullbackCompatible_iff`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryTheory.Functor Cᵒᵖ (Type
 w)) {B : C}   {I : Type u_1} {X : I → C} (…
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.SecondObj.ext`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Functor Cᵒᵖ (Type w
)) {B : C} {I : Type t}   [inst_1 : Small.{w…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Limits.Types.Small.productIso_hom_comp_eval_apply`：∀ {J :
 Type v} (F : J → Type u) [inst : Small.{u, v} J] (j : J) (x : ∏ᶜ F),   (equivSh
rink ((j : J) → F j)).symm       ((CategoryTheory.Conc…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Version of `CategoryTheory.Equalizer.Presieve.Arrows.compatible_iff` for a small
indexing type.
-/
lemma compatible_iff_of_small (x : FirstObj P X) :
    (Arrows.Compatible P π ((equivShrink _).symm ((Types.Small.productIso _).hom x))) ↔
      firstMap P X π x = secondMap P X π x := by
  rw [Arrows.pullbackCompatible_iff]
  refine ⟨fun t ↦ ?_, fun t i j ↦ ?_⟩
  · ext ij
    simpa [firstMap, secondMap] using t ij.1 ij.2
  · apply_fun Pi.π (fun (ij : I × I) ↦ P.obj (op (pullback (π ij.1) (π ij.2)))) ⟨i, j⟩ at t
    simpa [firstMap, secondMap] using t

set_option backward.isDefEq.respectTransparency.types false in
/-- `P` is a sheaf for `Presieve.ofArrows X π`, iff the fork given by `w` is an equalizer. -/
@[stacks 00VM]
/-
**CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Equalizer.Presieve.Arrows`。
形式化陈述：sheaf_condition : (Presieve.ofArrows X π).IsSheafFor P ↔ Nonempty (IsLimit
 (Fork.ofι (forkMap P X π) (w P X π)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.w`：w : forkMap P X π ≫ firstMap
 P X π = forkMap P X π ≫ secondMap P X π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `CategoryTheory.Presieve.isSheafFor_arrows_iff`：isSheafFor_arrows_iff : (
ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I) -> P.obj (op (X i))), Arrows.C
ompatible P π x -> exists! t, foral…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `existsUnique_congr`：existsUnique_congr {p q : α -> Prop} (h : forall a, 
p a ↔ q a) : (exists! a, p a) ↔ exists! a, q a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Types.Small.productIso_hom_comp_eval_apply`：∀ {J :
 Type v} (F : J → Type u) [inst : Small.{u, v} J] (j : J) (x : ∏ᶜ F),   (equivSh
rink ((j : J) → F j)).symm       ((CategoryTheory.Conc…
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`P` is a sheaf for `Presieve.ofArrows X π`, iff the fork given by `w` is an equa
lizer.
-/
theorem sheaf_condition : (Presieve.ofArrows X π).IsSheafFor P ↔
    Nonempty (IsLimit (Fork.ofι (forkMap P X π) (w P X π))) := by
  rw [Types.type_equalizer_iff_unique, isSheafFor_arrows_iff]
  simp only [FirstObj]
  rw [← Equiv.forall_congr_right ((equivShrink _).trans (Types.Small.productIso _).toEquiv.symm)]
  simp_rw [← compatible_iff_of_small, ← Iso.toEquiv_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  apply forall₂_congr
  intro x _
  apply existsUnique_congr
  intro t
  rw [Equiv.eq_symm_apply, ← Equiv.symm_apply_eq]
  constructor
  · intro q
    funext i
    simpa [Iso.toEquiv, forkMap] using q i
  · intro q i
    rw [← q]
    simp [Iso.toEquiv, forkMap]

end Arrows

/-- The sheaf condition for a single morphism is the same as the canonical fork diagram being
limiting. -/
/-
**CategoryTheory.Equalizer.Presieve.isSheafFor_singleton_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Equalizer.Presieve`。
形式化陈述：isSheafFor_singleton_iff {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y} (c : Pull
backCone f f) (hc : IsLimit c) : Presieve.IsSheafFor F (.singleton f) ↔ Nonempty
 (IsLimit (Fork.ofι (F.map f.op) (f
参数：c : PullbackCone f f；hc : IsLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用引理 `CategoryTheory.Presieve.isSheafFor_singleton`：isSheafFor_singleton {X Y 
: C} {f : X ⟶ Y} : Presieve.IsSheafFor P (.singleton f) ↔ forall (x : P.obj (op 
X)), (forall {Z : C} (p₁ p₂ : Z ⟶ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The sheaf condition for a single morphism is the same as the canonical fork diag
ram being
limiting.
-/
lemma isSheafFor_singleton_iff {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    (c : PullbackCone f f) (hc : IsLimit c) :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map c.fst.op) (g := F.map c.snd.op)
          (by simp [← Functor.map_comp, ← op_comp, c.condition]))) := by
  have h (x : F.obj (op X)) : (∀ {Z : C} (p₁ p₂ : Z ⟶ X),
      p₁ ≫ f = p₂ ≫ f → F.map p₁.op x = F.map p₂.op x) ↔ F.map c.fst.op x = F.map c.snd.op x := by
    refine ⟨fun H ↦ H _ _ c.condition, fun H Z p₁ p₂ h ↦ ?_⟩
    rw [← PullbackCone.IsLimit.lift_fst hc _ _ h, op_comp, Functor.map_comp, comp_apply, H]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  rw [Types.type_equalizer_iff_unique, Presieve.isSheafFor_singleton]
  simp_rw [h]

/-- Special case of `isSheafFor_singleton_iff` with `c = pullback.cone f f`. -/
/-
**CategoryTheory.Equalizer.Presieve.isSheafFor_singleton_iff_of_hasPullback** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Equalizer.Presieve`。
形式化陈述：isSheafFor_singleton_iff_of_hasPullback {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X
 ⟶ Y} [HasPullback f f] : Presieve.IsSheafFor F (.singleton f) ↔ Nonempty (IsLim
it (Fork.ofι (F.map f.op) (f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Equalizer.Presieve.isSheafFor_singleton_iff`：isSheafFor_s
ingleton_iff {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y} (c : PullbackCone f f) (hc 
: IsLimit c) : Presieve.IsSheafFor F (.singleton…

--- 原说明 ---
Special case of `isSheafFor_singleton_iff` with `c = pullback.cone f f`.
-/
lemma isSheafFor_singleton_iff_of_hasPullback {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    [HasPullback f f] :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map (pullback.fst f f).op)
          (g := F.map (pullback.snd f f).op)
          (by simp [← Functor.map_comp, ← op_comp, pullback.condition]))) :=
  isSheafFor_singleton_iff (pullback.cone f f) (pullback.isLimit f f)

end Presieve

end

end Equalizer

end CategoryTheory

