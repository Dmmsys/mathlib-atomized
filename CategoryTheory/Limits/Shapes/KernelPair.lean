/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f`
then it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `IsLimit (PullbackCone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/

@[expose] public section


universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

/-- `IsKernelPair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫ f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is just an abbreviation for `IsPullback a b f f`.
-/
/-
**CategoryTheory.IsKernelPair** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsKernelPair
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsKernelPair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫
 f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is just an abbreviation for `IsPullback a b f f`.
-/
abbrev IsKernelPair :=
  IsPullback a b f f

namespace IsKernelPair

/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
/-
**CategoryTheory.IsKernelPair.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsKerne
lPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data expressing that `(a, b)` is a kernel pair is subsingleton.
-/
instance : Subsingleton (IsKernelPair f a b) :=
  ⟨fun P Q => by constructor⟩

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)` is a kernel pair for `f`. -/
/-
**CategoryTheory.IsKernelPair.id_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsKernelPair`。
形式化陈述：id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…

--- 原说明 ---
If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)` is a kernel pair for `f`.
-/
theorem id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩
/-
**CategoryTheory.IsKernelPair.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsKerne
lPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨id_of_mono f⟩

variable {f a b}

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
/-
**CategoryTheory.IsKernelPair.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsK
ernelPair`。
形式化陈述：lift {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : 
S ⟶ R
参数：k : IsKernelPair f a b；p q : S ⟶ X；w : p ≫ f = q ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor 
through any kernel
pair of `f`.
-/
noncomputable def lift {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    S ⟶ R :=
  PullbackCone.IsLimit.lift k.isLimit _ _ w

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsKernelPair.lift_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.IsKernelPair`。
形式化陈述：lift_fst {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f
) : k.lift p q w ≫ a = p
参数：k : IsKernelPair f a b；p q : S ⟶ X；w : p ≫ f = q ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma lift_fst {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ a = p :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsKernelPair.lift_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.IsKernelPair`。
形式化陈述：lift_snd {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f
) : k.lift p q w ≫ b = q
参数：k : IsKernelPair f a b；p q : S ⟶ X；w : p ≫ f = q ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma lift_snd {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ b = q :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
/-
**CategoryTheory.IsKernelPair.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
KernelPair`。
形式化陈述：lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
 { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q }
参数：k : IsKernelPair f a b；p q : S ⟶ X；w : p ≫ f = q ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor 
through any kernel
pair of `f`.
-/
noncomputable def lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
  ⟨k.lift p q w, by simp⟩

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
/-
**CategoryTheory.IsKernelPair.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsKernelPair`。
形式化陈述：cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁) (big_k : I
sKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b
参数：comm : a ≫ f₁ = b ≫ f₁；big_k : IsKernelPair (f₁ ≫ f₂) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : 
CategoryTheory.Limits.PullbackCone f g) …
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Limits.PullbackCone.equalizer_ext`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : Ca
tegoryTheory.Limits.PullbackCone f g) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is
 a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show
 the square
commutes, rather than to additionally show it's a pullback.
-/
theorem cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  { w := comm
    isLimit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
        let s' : PullbackCone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          PullbackCone.mk s.fst s.snd (s.condition_assoc _)
        refine ⟨big_k.isLimit.lift s', big_k.isLimit.fac _ WalkingCospan.left,
          big_k.isLimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isLimit.hom_ext
        refine (PullbackCone.mk a b ?_ : PullbackCone (f₁ ≫ f₂) _).equalizer_ext ?_ ?_
        · apply reassoc_of% comm
        · apply m₁.trans (big_k.isLimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isLimit.fac s' WalkingCospan.right).symm⟩ }

/-- If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
/-
**CategoryTheory.IsKernelPair.cancel_right_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsKernelPair`。
形式化陈述：cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (big_k : IsKernel
Pair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b
参数：big_k : IsKernelPair (f₁ ≫ f₂) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsKernelPair.cancel_right`：cancel_right {f₁ : X ⟶ Y} {f₂ 
: Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁) (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKerne
lPair f₁ a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…

--- 原说明 ---
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a ke
rnel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
theorem cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂]
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k

set_option backward.isDefEq.respectTransparency false in
/--
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
/-
**CategoryTheory.IsKernelPair.comp_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsKernelPair`。
形式化陈述：comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f
₁ a b) : IsKernelPair (f₁ ≫ f₂) a b
参数：small_k : IsKernelPair f₁ a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `CategoryTheory.IsKernelPair.lift_fst`：lift_fst {S : C} (k : IsKernelPair
 f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : k.lift p q w ≫ a = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `CategoryTheory.IsKernelPair.lift_snd`：lift_snd {S : C} (k : IsKernelPair
 f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : k.lift p q w ≫ b = q
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Limits.PullbackCone.equalizer_ext`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : Ca
tegoryTheory.Limits.PullbackCone f g) …

--- 原说明 ---
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel 
pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
theorem comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b) :
    IsKernelPair (f₁ ≫ f₂) a b :=
  { w := by rw [small_k.w_assoc]
    isLimit' := ⟨by
      refine PullbackCone.isLimitAux _
        (fun s => small_k.lift s.fst s.snd (by rw [← cancel_mono f₂, assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isLimit.hom_ext
      apply PullbackCone.equalizer_ext small_k.cone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

set_option backward.isDefEq.respectTransparency false in
/--
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
/-
**CategoryTheory.IsKernelPair.toCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.IsKernelPair`。
形式化陈述：toCoequalizer (k : IsKernelPair f a b) (r : RegularEpi f) : IsColimit (Cof
ork.ofπ f k.w)
参数：k : IsKernelPair f a b；r : RegularEpi f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some
 parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
noncomputable def toCoequalizer (k : IsKernelPair f a b) (r : RegularEpi f) :
    IsColimit (Cofork.ofπ f k.w) := by
  let t := k.isLimit.lift (PullbackCone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.isLimit.fac _ WalkingCospan.left
  have kt : t ≫ b = r.right := k.isLimit.fac _ WalkingCospan.right
  refine Cofork.IsColimit.mk _
    (fun s => Cofork.IsColimit.desc r.isColimit s.π
      (by rw [← ht, assoc, s.condition, reassoc_of% kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Cofork.IsColimit.π_desc' r.isColimit
  · apply Cofork.IsColimit.hom_ext r.isColimit
    exact w.trans (Cofork.IsColimit.π_desc' r.isColimit _ _).symm

/--
If `(a,b)` is the kernel pair of `f`, and `f` is a regular epimorphism, then
`f` is a coequalizer morphism of `a` and `b`.
-/
/-
**CategoryTheory.IsKernelPair.toCoequalizer'** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.IsKernelPair`。
形式化陈述：toCoequalizer' (k : IsKernelPair f a b) [IsRegularEpi f] : IsColimit (Cofo
rk.ofπ f k.w)
参数：k : IsKernelPair f a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(a,b)` is the kernel pair of `f`, and `f` is a regular epimorphism, then
`f` is a coequalizer morphism of `a` and `b`.
-/
noncomputable def toCoequalizer' (k : IsKernelPair f a b) [IsRegularEpi f] :
    IsColimit (Cofork.ofπ f k.w) :=
  toCoequalizer k <| IsRegularEpi.getStruct f

set_option backward.isDefEq.respectTransparency false in
/-- If `a₁ a₂ : A ⟶ Y` is a kernel pair for `g : Y ⟶ Z`, then `a₁ ×[Z] X` and `a₂ ×[Z] X`
(`A ×[Z] X ⟶ Y ×[Z] X`) is a kernel pair for `Y ×[Z] X ⟶ X`. -/
/-
**CategoryTheory.IsKernelPair.pullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsKernelPair`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z A : C} {g 
: Y ⟶ Z} {a₁ a₂ : A ⟶ Y}   (h : CategoryTheory.IsKernelPair g a₁ a₂) (f : X ⟶ Z)
 [inst_1 : CategoryTheory.Limits.HasPullback f g]   [inst_2 : CategoryTheory.Lim
its.HasPullback f (CategoryTheory.CategoryStruct.comp a₁ g)],   CategoryTheory.I
sKernelPair (CategoryTheory.Limits.pullback.fst f g)     (CategoryTheory.Limits.
pullback.map f (CategoryTheory.CategoryStruct.comp a₁ g) f g       (CategoryTheo
ry.CategoryStruct.id X) a₁ (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯)     (Catego
ryTheory.Limits.pullback.map f (CategoryTheory.CategoryStruct.comp a₁ g) f g    
   (CategoryTheory.CategoryStruct.id X) a₂ (CategoryTheory.CategoryStruct.id Z) 
⋯ ⋯)
参数：h : CategoryTheory.IsKernelPair g a₁ a₂；f : X ⟶ Z；CategoryTheory.CategoryStru
ct.comp a₁ g；CategoryTheory.Limits.pullback.fst f g；CategoryTheory.Limits.pullba
ck.map f (CategoryTheory.CategoryStruct.comp a₁ g) f g       (CategoryTheory.Cat
egoryStruct.id X) a₁ (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯；CategoryTheory.Lim
its.pullback.map f (CategoryTheory.CategoryStruct.comp a₁ g) f g       (Category
Theory.CategoryStruct.id X) a₂ (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsKernelPair.lift_fst_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {R X Y : C} {f : X ⟶ Y} {a b : R ⟶ X} {S : C}   (k 
: CategoryTheory.IsKernelPair f …
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用引理 `CategoryTheory.IsKernelPair.lift_fst`：lift_fst {S : C} (k : IsKernelPair
 f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : k.lift p q w ≫ a = p
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
· 使用引理 `CategoryTheory.IsKernelPair.lift_snd`：lift_snd {S : C} (k : IsKernelPair
 f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : k.lift p q w ≫ b = q
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …

--- 原说明 ---
If `a₁ a₂ : A ⟶ Y` is a kernel pair for `g : Y ⟶ Z`, then `a₁ ×[Z] X` and `a₂ ×[
Z] X`
(`A ×[Z] X ⟶ Y ×[Z] X`) is a kernel pair for `Y ×[Z] X ⟶ X`.
-/
protected theorem pullback {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
    (f : X ⟶ Z) [HasPullback f g] [HasPullback f (a₁ ≫ g)] :
    IsKernelPair (pullback.fst f g)
      (pullback.map f _ f _ (𝟙 X) a₁ (𝟙 Z) (by simp) <| Category.comp_id _)
      (pullback.map _ _ _ _ (𝟙 X) a₂ (𝟙 Z) (by simp) <| (Category.comp_id _).trans h.1.1) := by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s (m : _ ⟶ pullback f (a₁ ≫ g)) hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · apply pullback.hom_ext
    · simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsKernelPair.mono_of_isIso_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsKernelPair`。
形式化陈述：mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f
参数：h : IsKernelPair f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.cone_fst`：cone_fst (h : IsPullback fst snd f g
) : h.cone.fst = fst
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
-/
theorem mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f := by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp)
  rw [IsPullback.cone_fst, ← IsIso.eq_comp_inv, Category.id_comp] at h₁
  rw [h₁, IsIso.inv_comp_eq, Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst, h₂]
/-
**CategoryTheory.IsKernelPair.mono_of_eq_fst_snd'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsKernelPair`。
形式化陈述：mono_of_eq_fst_snd' (h : IsKernelPair f a a) : Mono f
参数：h : IsKernelPair f a a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsKernelPair.lift_fst`：lift_fst {S : C} (k : IsKernelPair
 f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : k.lift p q w ≫ a = p
· 使用引理 `CategoryTheory.IsKernelPair.lift_snd`：lift_snd {S : C} (k : IsKernelPair
 f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : k.lift p q w ≫ b = q
-/
theorem mono_of_eq_fst_snd' (h : IsKernelPair f a a) : Mono f :=
  ⟨fun g₁ g₂ e ↦ (lift_fst h g₁ g₂ e).symm.trans <| lift_snd h g₁ g₂ e⟩
/-
**CategoryTheory.IsKernelPair.mono_of_eq_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsKernelPair`。
形式化陈述：mono_of_eq_fst_snd (h : IsKernelPair f a b) (e : a = b) : Mono f
参数：h : IsKernelPair f a b；e : a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsKernelPair.mono_of_eq_fst_snd'`：mono_of_eq_fst_snd' (h 
: IsKernelPair f a a) : Mono f
-/
theorem mono_of_eq_fst_snd (h : IsKernelPair f a b) (e : a = b) : Mono f := by
  induction e; exact h.mono_of_eq_fst_snd'

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.IsKernelPair.isIso_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsKernelPair`。
形式化陈述：isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a
参数：h : IsKernelPair f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
theorem isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a := by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance
/-
**CategoryTheory.IsKernelPair.of_isIso_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.IsKernelPair`。
形式化陈述：of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.IsKernelPair.id_of_mono`：id_of_mono [Mono f] : IsKernelPa
ir f (𝟙 _) (𝟙 _)
-/
theorem of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a := by
  change IsPullback _ _ _ _
  convert! (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _)⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }

/-- The kernel pair provided by `HasPullback f f` fits into an `IsKernelPair`. -/
/-
**CategoryTheory.IsKernelPair.of_hasPullback** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.IsKernelPair`。
形式化陈述：of_hasPullback (f : X ⟶ Y) [HasPullback f f] : IsKernelPair f (pullback.fs
t f f) (pullback.snd f f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g

--- 原说明 ---
The kernel pair provided by `HasPullback f f` fits into an `IsKernelPair`.
-/
theorem of_hasPullback (f : X ⟶ Y) [HasPullback f f] :
    IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end IsKernelPair

/-
**CategoryTheory.IsRegularEpi.exists_of_isKernelPair** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.IsRegularEpi`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (π : X 
⟶ Y) [CategoryTheory.IsRegularEpi π] {Z : C}   {fst snd : Z ⟶ X},   CategoryTheo
ry.IsKernelPair π fst snd →     ∀ {W : C} (f : X ⟶ W),       CategoryTheory.Cate
goryStruct.comp fst f = CategoryTheory.CategoryStruct.comp snd f →         ∃ g, 
CategoryTheory.CategoryStruct.comp π g = f
参数：π : X ⟶ Y；f : X ⟶ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc`：∀ {C : Type u} {X Y : C} 
[inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryTheory.
Limits.Cofork f g} (hs : CategoryTh…
-/
lemma IsRegularEpi.exists_of_isKernelPair {X Y : C} (π : X ⟶ Y) [IsRegularEpi π] {Z : C}
    {fst snd : Z ⟶ X} (h : IsKernelPair π fst snd) {W : C} (f : X ⟶ W) (w : fst ≫ f = snd ≫ f) :
    ∃ (g : Y ⟶ W), π ≫ g = f :=
  ⟨h.toCoequalizer'.desc (Cofork.ofπ f w), Cofork.IsColimit.π_desc h.toCoequalizer'⟩

end CategoryTheory

