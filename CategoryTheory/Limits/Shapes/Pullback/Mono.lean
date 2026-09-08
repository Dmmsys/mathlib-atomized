/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Pullbacks and monomorphisms

This file provides some results about interactions between pullbacks and monomorphisms, as well as
the dual statements between pushouts and epimorphisms.

## Main results
* Monomorphisms are stable under pullback. This is available using the `PullbackCone` API as
  `mono_fst_of_is_pullback_of_mono` and `mono_snd_of_is_pullback_of_mono`, and using the `pullback`
  API as `pullback.fst_of_mono` and `pullback.snd_of_mono`.

* A pullback cone is a limit iff its composition with a monomorphism is a limit. This is available
  as `IsLimitOfCompMono` and `pullbackIsPullbackOfCompMono` respectively.

* Monomorphisms admit kernel pairs, this is `has_kernel_pair_of_mono`.

The dual notions for pushouts are also available.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom PullbackCone

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

section Monomorphisms

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Monomorphisms are stable under pullback in the first argument. -/
/-
**CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [M
ono f] : Mono t.snd
参数：ht : IsLimit t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h

--- 原说明 ---
Monomorphisms are stable under pullback in the first argument.
-/
theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] :
    Mono t.snd := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  rw [← cancel_mono f, Category.assoc, Category.assoc, condition]
  apply reassoc_of% i

/-- Monomorphisms are stable under pullback in the second argument. -/
/-
**CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [M
ono g] : Mono t.fst
参数：ht : IsLimit t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h

--- 原说明 ---
Monomorphisms are stable under pullback in the second argument.
-/
theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← condition]
  apply reassoc_of% i

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
/-
**CategoryTheory.Limits.PullbackCone.isLimitMkIdId** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : Pullbac
kCone f f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono
. The converse is
shown in `mono_of_pullback_is_id`.
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun _ => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `PullbackCone.is_id_of_mono`.
-/
/-
**CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : Pullb
ackCone f f)) : Mono f
参数：f : X ⟶ Y；t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`
. The converse is
given in `PullbackCone.is_id_of_mono`.
-/
theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
`x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and `y`. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitOfFactors** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) 
(y : Y ⟶ W) (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsL
imit s) : IsLimit (PullbackCone.mk _ _ (show s.fst ≫ x = s.snd ≫ y from (cancel_
mono h).1 by simp only [Category.assoc, hxh, hyh, s.condition]))
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ Z；x : X ⟶ W；y : Y ⟶ W；hxh : x ≫ h = f；hyh : y ≫ h
 = g；s : PullbackCone f g；hs : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit 
cone over the
diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomor
phism `h` via
`x` and `y`, respectively.  Then `s` is also a limit cone over the diagram forme
d by `x` and `y`.
-/
def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
    (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
          (cancel_mono h).1 <| by simp only [Category.assoc, hxh, hyh, s.condition])) :=
  PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by  -- Porting note: reassoc workaround
      rw [← Category.assoc, ← Category.assoc]
      apply congrArg (· ≫ h) t.condition
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun hr hr' => by
        apply PullbackCone.IsLimit.hom_ext hs <;>
              simp only [PullbackCone.mk_fst, PullbackCone.mk_snd] at hr hr' ⊢ <;>
            simp only [hr, hr'] <;>
          symm
        exacts [hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right]⟩⟩

/-- If `W` is the pullback of `f, g`, it is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitOfCompMono** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : Pullba
ckCone f g) (H : IsLimit s) : IsLimit (PullbackCone.mk _ _ (show s.fst ≫ f ≫ i =
 s.snd ≫ g ≫ i by rw [← Category.assoc]; rw [← Category.assoc]; rw [s.condition]
))
参数：f : X ⟶ W；g : Y ⟶ W；i : W ⟶ Z；s : PullbackCone f g；H : IsLimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W` is the pullback of `f, g`, it is also the pullback of `f ≫ i, g ≫ i` for 
any mono `i`.
-/
def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
    (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← Category.assoc, ← Category.assoc, s.condition])) := by
  apply PullbackCone.isLimitAux'
  intro s
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PullbackCone

end Monomorphisms

/-- The pullback of a monomorphism is a monomorphism -/
/-
**CategoryTheory.Limits.pullback.fst_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g] [CategoryT
heory.Mono g],   CategoryTheory.Mono (CategoryTheory.Limits.pullback.fst f g)
参数：CategoryTheory.Limits.pullback.fst f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono`：mono
_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] : M
ono t.fst

--- 原说明 ---
The pullback of a monomorphism is a monomorphism
-/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst f g) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)

/-- The pullback of a monomorphism is a monomorphism -/
/-
**CategoryTheory.Limits.pullback.snd_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g] [CategoryT
heory.Mono f],   CategoryTheory.Mono (CategoryTheory.Limits.pullback.snd f g)
参数：CategoryTheory.Limits.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono`：mono
_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] : M
ono t.snd

--- 原说明 ---
The pullback of a monomorphism is a monomorphism
-/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd f g) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
/-
**CategoryTheory.Limits.mono_pullback_to_prod** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：mono_pullback_to_prod {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Z) (g
 : Y ⟶ Z) [HasPullback f g] [HasBinaryProduct X Y] : Mono (prod.lift (pullback.f
st f g) (pullback.snd f g))
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…

--- 原说明 ---
The map `X ×[Z] Y ⟶ X × Y` is mono.
-/
instance mono_pullback_to_prod {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ prod.fst) h
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩

/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
/-
**CategoryTheory.Limits.pullbackIsPullbackOfCompMono** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] 
[HasPullback f g] : IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f 
g) -- Porting note: following used to be _ (show (pullback.fst f g) ≫ f ≫ i = (p
ullback.snd f g) ≫ g ≫ i by simp only [← Category.assoc]; rw [cancel_mono]; appl
y pullback.condition))
参数：f : X ⟶ W；g : Y ⟶ W；i : W ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`.
-/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g)
      -- Porting note: following used to be _
      (show (pullback.fst f g) ≫ f ≫ i = (pullback.snd f g) ≫ g ≫ i by
        simp only [← Category.assoc]; rw [cancel_mono]; apply pullback.condition)) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))
/-
**CategoryTheory.Limits.hasPullback_of_comp_mono** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [Has
Pullback f g] : HasPullback (f ≫ i) (g ≫ i)
参数：f : X ⟶ W；g : Y ⟶ W；i : W ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩

section

attribute [local instance] hasPullback_of_left_iso

variable (f : X ⟶ Z) (i : Z ⟶ W) [Mono i]

/-
**CategoryTheory.Limits.hasPullback_of_right_factors_mono** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasPullback_of_right_factors_mono : HasPullback i (f ≫ i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.hasPullback_of_left_iso`：hasPullback_of_left_iso :
 HasPullback f g
-/
instance hasPullback_of_right_factors_mono : HasPullback i (f ≫ i) := by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono (𝟙 Z) f i

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_snd_iso_of_right_factors_mono : IsIso (pullback.snd i (f ≫ i))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_of_left_iso`：hasPullback_of_left_iso :
 HasPullback f g
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance pullback_snd_iso_of_right_factors_mono :
    IsIso (pullback.snd i (f ≫ i)) := by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  convert! (congrArg IsIso (show _ ≫ pullback.snd (𝟙 Z) f = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

attribute [local instance] hasPullback_of_right_iso
/-
**CategoryTheory.Limits.hasPullback_of_left_factors_mono** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasPullback_of_left_factors_mono : HasPullback (f ≫ i) i
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.hasPullback_of_right_iso`：hasPullback_of_right_iso
 : HasPullback f g
-/
instance hasPullback_of_left_factors_mono : HasPullback (f ≫ i) i := by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono f (𝟙 Z) i

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_snd_iso_of_left_factors_mono : IsIso (pullback.fst (f ≫ i) i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_of_right_iso`：hasPullback_of_right_iso
 : HasPullback f g
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance pullback_snd_iso_of_left_factors_mono :
    IsIso (pullback.fst (f ≫ i) i) := by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  convert! (congrArg IsIso (show _ ≫ pullback.fst f (𝟙 Z) = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

end

section

open WalkingCospan

variable (f : X ⟶ Y) [Mono f]

/-
**CategoryTheory.Limits.has_kernel_pair_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：has_kernel_pair_of_mono : HasPullback f f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance has_kernel_pair_of_mono : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩
/-
**CategoryTheory.Limits.PullbackCone.fst_eq_snd_of_mono_eq** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y} [CategoryTheory.Mono f]   (t : CategoryTheory.Limits.PullbackCone f f), t.f
st = t.snd
参数：t : CategoryTheory.Limits.PullbackCone f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
-/
theorem PullbackCone.fst_eq_snd_of_mono_eq {f : X ⟶ Y} [Mono f] (t : PullbackCone f f) :
    t.fst = t.snd :=
  (cancel_mono f).1 t.condition
/-
**CategoryTheory.Limits.fst_eq_snd_of_mono_eq** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：fst_eq_snd_of_mono_eq : pullback.fst f f = pullback.snd f f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.fst_eq_snd_of_mono_eq`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [CategoryTheory
.Mono f]   (t : CategoryTheory.Limits.Pullback…
-/
theorem fst_eq_snd_of_mono_eq : pullback.fst f f = pullback.snd f f :=
  PullbackCone.fst_eq_snd_of_mono_eq (getLimitCone (cospan f f)).cone

@[simp]
/-
**CategoryTheory.Limits.pullbackSymmetry_hom_of_mono_eq** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：pullbackSymmetry_hom_of_mono_eq : (pullbackSymmetry f f).hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.fst_eq_snd_of_mono_eq`：fst_eq_snd_of_mono_eq : pul
lback.fst f f = pullback.snd f f
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackSymmetry_hom_of_mono_eq : (pullbackSymmetry f f).hom = 𝟙 _ := by
  ext
  · simp [fst_eq_snd_of_mono_eq]
  · simp [fst_eq_snd_of_mono_eq]

variable {f} in
/-
**CategoryTheory.Limits.PullbackCone.isIso_fst_of_mono_of_isLimit** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y} [CategoryTheory.Mono f]   {t : CategoryTheory.Limits.PullbackCone f f} (ht 
: CategoryTheory.Limits.IsLimit t), CategoryTheory.IsIso t.fst
参数：ht : CategoryTheory.Limits.IsLimit t。
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
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PullbackCone.fst_eq_snd_of_mono_eq`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [CategoryTheory
.Mono f]   (t : CategoryTheory.Limits.Pullback…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma PullbackCone.isIso_fst_of_mono_of_isLimit {t : PullbackCone f f} (ht : IsLimit t) :
    IsIso t.fst := by
  refine ⟨⟨PullbackCone.IsLimit.lift ht (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩⟩
  apply PullbackCone.IsLimit.hom_ext ht
  · simp
  · simp [fst_eq_snd_of_mono_eq]

variable {f} in
/-
**CategoryTheory.Limits.PullbackCone.isIso_snd_of_mono_of_isLimit** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y} [CategoryTheory.Mono f]   {t : CategoryTheory.Limits.PullbackCone f f} (ht 
: CategoryTheory.Limits.IsLimit t), CategoryTheory.IsIso t.snd
参数：ht : CategoryTheory.Limits.IsLimit t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.isIso_fst_of_mono_of_isLimit`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categor
yTheory.Mono f]   {t : CategoryTheory.Limits.Pullback…
· 使用定理 `CategoryTheory.Limits.PullbackCone.fst_eq_snd_of_mono_eq`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [CategoryTheory
.Mono f]   (t : CategoryTheory.Limits.Pullback…
-/
lemma PullbackCone.isIso_snd_of_mono_of_isLimit {t : PullbackCone f f} (ht : IsLimit t) :
    IsIso t.snd :=
  t.fst_eq_snd_of_mono_eq ▸ t.isIso_fst_of_mono_of_isLimit ht
/-
**CategoryTheory.Limits.isIso_fst_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：isIso_fst_of_mono : IsIso (pullback.fst f f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.isIso_fst_of_mono_of_isLimit`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categor
yTheory.Mono f]   {t : CategoryTheory.Limits.Pullback…
-/
instance isIso_fst_of_mono : IsIso (pullback.fst f f) :=
  PullbackCone.isIso_fst_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit
/-
**CategoryTheory.Limits.isIso_snd_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：isIso_snd_of_mono : IsIso (pullback.snd f f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.isIso_snd_of_mono_of_isLimit`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categor
yTheory.Mono f]   {t : CategoryTheory.Limits.Pullback…
-/
instance isIso_snd_of_mono : IsIso (pullback.snd f f) :=
  PullbackCone.isIso_snd_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit
end

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-
**CategoryTheory.Limits.PushoutCocone.epi_inr_of_is_pushout_of_epi** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [E
pi f] : Epi t.inr
参数：ht : IsColimit t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {t
 : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition_assoc`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (t :
 CategoryTheory.Limits.PushoutCocone f g)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] :
    Epi t.inr :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩
/-
**CategoryTheory.Limits.PushoutCocone.epi_inl_of_is_pushout_of_epi** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [E
pi g] : Epi t.inl
参数：ht : IsColimit t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {t
 : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition_assoc`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (t :
 CategoryTheory.Limits.PushoutCocone f g)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] :
    Epi t.inl :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩

/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_isColimit_mk_id_id`.
-/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitMkIdId** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : Push
outCocone f f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an 
epi. The converse is
shown in `epi_of_isColimit_mk_id_id`.
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun _ => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
    simpa using m₁

/-- `f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `PushoutCocone.isColimitMkIdId`.
-/
/-
**CategoryTheory.Limits.PushoutCocone.epi_of_isColimitMkIdId** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：epi_of_isColimitMkIdId (f : X ⟶ Y) (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : Pu
shoutCocone f f)) : Epi f
参数：f : X ⟶ Y；t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, 
f)`.
The converse is given in `PushoutCocone.isColimitMkIdId`.
-/
theorem epi_of_isColimitMkIdId (f : X ⟶ Y)
    (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
`x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
`y`. -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitOfFactors** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y)
 (y : W ⟶ Z) (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : I
sColimit s) : have reassoc₁ : h ≫ x ≫ inl s = f ≫ inl s
参数：f : X ⟶ Y；g : X ⟶ Z；h : X ⟶ W；x : W ⟶ Y；y : W ⟶ Z；hhx : h ≫ x = f；hhy : h ≫ y
 = g；s : PushoutCocone f g；hs : IsColimit s。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit 
cocone over the
diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimor
phism `h` via
`x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram fo
rmed by `x` and
`y`.
-/
def isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
    (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : IsColimit s) :
    have reassoc₁ : h ≫ x ≫ inl s = f ≫ inl s := by  -- Porting note: working around reassoc
      rw [← Category.assoc]; apply congrArg (· ≫ inl s) hhx
    have reassoc₂ : h ≫ y ≫ inr s = g ≫ inr s := by
      rw [← Category.assoc]; apply congrArg (· ≫ inr s) hhy
    IsColimit (PushoutCocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr from
          (cancel_epi h).1 <| by rw [reassoc₁, reassoc₂, s.condition])) :=
  PushoutCocone.isColimitAux' _ fun t => ⟨hs.desc (PushoutCocone.mk t.inl t.inr <| by
    rw [← hhx, ← hhy, Category.assoc, Category.assoc, t.condition]),
      ⟨hs.fac _ WalkingSpan.left, hs.fac _ WalkingSpan.right, fun hr hr' => by
        apply PushoutCocone.IsColimit.hom_ext hs
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr]
          symm
          exact hs.fac _ WalkingSpan.left
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr']
          symm
          exact hs.fac _ WalkingSpan.right⟩⟩

/-- If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`. -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitOfEpiComp** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : Pushou
tCocone f g) (H : IsColimit s) : IsColimit (PushoutCocone.mk _ _ (show (h ≫ f) ≫
 s.inl = (h ≫ g) ≫ s.inr by rw [Category.assoc]; rw [Category.assoc]; rw [s.cond
ition]))
参数：f : X ⟶ Y；g : X ⟶ Z；h : W ⟶ X；s : PushoutCocone f g；H : IsColimit s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`.
-/
def isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
    (H : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr by
          rw [Category.assoc, Category.assoc, s.condition])) := by
  apply PushoutCocone.isColimitAux'
  intro s
  rcases PushoutCocone.IsColimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PushoutCocone

/-- The pushout of an epimorphism is an epimorphism -/
/-
**CategoryTheory.Limits.pushout.inl_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g] [CategoryTh
eory.Epi g],   CategoryTheory.Epi (CategoryTheory.Limits.pushout.inl f g)
参数：CategoryTheory.Limits.pushout.inl f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.epi_inl_of_is_pushout_of_epi`：epi_in
l_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] : Epi 
t.inl

--- 原说明 ---
The pushout of an epimorphism is an epimorphism
-/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)

/-- The pushout of an epimorphism is an epimorphism -/
/-
**CategoryTheory.Limits.pushout.inr_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g] [CategoryTh
eory.Epi f],   CategoryTheory.Epi (CategoryTheory.Limits.pushout.inr f g)
参数：CategoryTheory.Limits.pushout.inr f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.epi_inr_of_is_pushout_of_epi`：epi_in
r_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] : Epi 
t.inr

--- 原说明 ---
The pushout of an epimorphism is an epimorphism
-/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr _ _ : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The map `X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
/-
**CategoryTheory.Limits.epi_coprod_to_pushout** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：epi_coprod_to_pushout {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g
 : X ⟶ Z) [HasPushout f g] [HasBinaryCoproduct Y Z] : Epi (coprod.desc (pushout.
inl f g) (pushout.inr f g))
参数：f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…

--- 原说明 ---
The map `X ⨿ Y ⟶ X ⨿[Z] Y` is epi.
-/
instance epi_coprod_to_pushout {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasBinaryCoproduct Y Z] :
    Epi (coprod.desc (pushout.inl f g) (pushout.inr f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩

/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
/-
**CategoryTheory.Limits.pushoutIsPushoutOfEpiComp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [Has
Pushout f g] : IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr f g) (
show (h ≫ f) ≫ pushout.inl f g = (h ≫ g) ≫ pushout.inr f g by simp only [Categor
y.assoc]; rw [cancel_epi]; exact pushout.condition))
参数：f : X ⟶ Y；g : X ⟶ Z；h : W ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`.
-/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
    [HasPushout f g] : IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr f g)
    (show (h ≫ f) ≫ pushout.inl f g = (h ≫ g) ≫ pushout.inr f g by
    simp only [Category.assoc]; rw [cancel_epi]; exact pushout.condition)) :=
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))
/-
**CategoryTheory.Limits.hasPushout_of_epi_comp** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPus
hout f g] : HasPushout (h ≫ f) (h ≫ g)
参数：f : X ⟶ Y；g : X ⟶ Z；h : W ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩

section

attribute [local instance] hasPushout_of_left_iso

variable (f : X ⟶ Z) (h : W ⟶ X) [Epi h]

/-
**CategoryTheory.Limits.hasPushout_of_right_factors_epi** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasPushout_of_right_factors_epi : HasPushout h (h ≫ f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.hasPushout_of_left_iso`：hasPushout_of_left_iso : H
asPushout f g
-/
instance hasPushout_of_right_factors_epi : HasPushout h (h ≫ f) := by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp (𝟙 X) f h

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout_inr_iso_of_right_factors_epi** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pushout_inr_iso_of_right_factors_epi : IsIso (pushout.inr _ _ : _ ⟶ pushou
t h (h ≫ f))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_of_left_iso`：hasPushout_of_left_iso : H
asPushout f g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance pushout_inr_iso_of_right_factors_epi :
    IsIso (pushout.inr _ _ : _ ⟶ pushout h (h ≫ f)) := by
  convert!
    (congrArg IsIso
          (show pushout.inr _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩
              WalkingSpan.right)).mp
      inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm

attribute [local instance] hasPushout_of_right_iso
/-
**CategoryTheory.Limits.hasPushout_of_left_factors_epi** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.hasPushout_of_right_iso`：hasPushout_of_right_iso :
 HasPushout f g
-/
instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp f (𝟙 X) h

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout_inl_iso_of_left_factors_epi** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) : IsIso (pushout.inl _ _ :
 _ ⟶ pushout (h ≫ f) h)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_of_right_iso`：hasPushout_of_right_iso :
 HasPushout f g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl _ _ : _ ⟶ pushout (h ≫ f) h) := by
  convert!
    (congrArg IsIso
          (show pushout.inl _ _ ≫ _ = _ from
            colimit.isoColimitCocone_ι_inv ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩
              WalkingSpan.left)).mp
      inferInstance
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

end

section

open WalkingSpan

variable (f : X ⟶ Y) [Epi f]

/-
**CategoryTheory.Limits.has_cokernel_pair_of_epi** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：has_cokernel_pair_of_epi : HasPushout f f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance has_cokernel_pair_of_epi : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩
/-
**CategoryTheory.Limits.PushoutCocone.inl_eq_inr_of_epi_eq** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y} [CategoryTheory.Epi f]   (t : CategoryTheory.Limits.PushoutCocone f f), t.i
nl = t.inr
参数：t : CategoryTheory.Limits.PushoutCocone f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
-/
theorem PushoutCocone.inl_eq_inr_of_epi_eq {f : X ⟶ Y} [Epi f] (t : PushoutCocone f f) :
    t.inl = t.inr :=
  (cancel_epi f).1 t.condition
/-
**CategoryTheory.Limits.inl_eq_inr_of_epi_eq** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：inl_eq_inr_of_epi_eq : pushout.inl f f = pushout.inr f f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.inl_eq_inr_of_epi_eq`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [CategoryTheory
.Epi f]   (t : CategoryTheory.Limits.PushoutCo…
-/
theorem inl_eq_inr_of_epi_eq : pushout.inl f f = pushout.inr f f :=
  PushoutCocone.inl_eq_inr_of_epi_eq (getColimitCocone (span f f)).cocone

@[simp]
/-
**CategoryTheory.Limits.pullback_symmetry_hom_of_epi_eq** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：pullback_symmetry_hom_of_epi_eq : (pushoutSymmetry f f).hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.inl_eq_inr_of_epi_eq`：inl_eq_inr_of_epi_eq : pusho
ut.inl f f = pushout.inr f f
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom`：inr_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inl _ _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullback_symmetry_hom_of_epi_eq : (pushoutSymmetry f f).hom = 𝟙 _ := by
  ext <;> simp [inl_eq_inr_of_epi_eq]

variable {f} in
/-
**CategoryTheory.Limits.PushoutCocone.isIso_inl_of_epi_of_isColimit** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y} [CategoryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCocone f f} (ht 
: CategoryTheory.Limits.IsColimit t), CategoryTheory.IsIso t.inl
参数：ht : CategoryTheory.Limits.IsColimit t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.inl_desc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {
t : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {t
 : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.inl_desc_assoc`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ 
Z}   {t : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.inl_eq_inr_of_epi_eq`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [CategoryTheory
.Epi f]   (t : CategoryTheory.Limits.PushoutCo…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.inr_desc_assoc`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ 
Z}   {t : CategoryTheory.Limits.PushoutCocone f g}…
-/
lemma PushoutCocone.isIso_inl_of_epi_of_isColimit {t : PushoutCocone f f} (ht : IsColimit t) :
    IsIso t.inl := by
  refine ⟨⟨PushoutCocone.IsColimit.desc ht (𝟙 _) (𝟙 _) (by simp), by simp, ?_⟩⟩
  apply PushoutCocone.IsColimit.hom_ext ht
  · simp
  · simp [inl_eq_inr_of_epi_eq]

variable {f} in
/-
**CategoryTheory.Limits.PushoutCocone.isIso_inr_of_epi_of_isColimit** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y} [CategoryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCocone f f} (ht 
: CategoryTheory.Limits.IsColimit t), CategoryTheory.IsIso t.inr
参数：ht : CategoryTheory.Limits.IsColimit t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.isIso_inl_of_epi_of_isColimit`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categ
oryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCo…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.inl_eq_inr_of_epi_eq`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [CategoryTheory
.Epi f]   (t : CategoryTheory.Limits.PushoutCo…
-/
lemma PushoutCocone.isIso_inr_of_epi_of_isColimit {t : PushoutCocone f f} (ht : IsColimit t) :
    IsIso t.inr :=
  t.inl_eq_inr_of_epi_eq ▸ t.isIso_inl_of_epi_of_isColimit ht
/-
**CategoryTheory.Limits.isIso_inl_of_epi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isIso_inl_of_epi : IsIso (pushout.inl f f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.isIso_inl_of_epi_of_isColimit`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categ
oryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCo…
-/
instance isIso_inl_of_epi : IsIso (pushout.inl f f) :=
  PushoutCocone.isIso_inl_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit
/-
**CategoryTheory.Limits.isIso_inr_of_epi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isIso_inr_of_epi : IsIso (pushout.inr f f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.isIso_inr_of_epi_of_isColimit`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} [Categ
oryTheory.Epi f]   {t : CategoryTheory.Limits.PushoutCo…
-/
instance isIso_inr_of_epi : IsIso (pushout.inr f f) :=
  PushoutCocone.isIso_inr_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

end

end CategoryTheory.Limits

