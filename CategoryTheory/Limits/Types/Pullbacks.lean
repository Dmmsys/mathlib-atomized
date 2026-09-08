/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Pullbacks in the category of types

In `Type*`, the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the
subtype `{ p : X × Y // f p.1 = g p.2 }` of the product.
We show some additional lemmas for pullbacks in the category of types.
-/

@[expose] public section

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} {X' Y' Z' : Type v}
variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')

/-- The usual explicit pullback in the category of types, as a subtype of the product.
The full `LimitCone` data is bundled as `pullbackLimitCone f g`.
-/
/-
**CategoryTheory.Limits.Types.PullbackObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.Types`。
形式化陈述：PullbackObj : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The usual explicit pullback in the category of types, as a subtype of the produc
t.
The full `LimitCone` data is bundled as `pullbackLimitCone f g`.
-/
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }

-- `PullbackObj f g` comes with a coercion to the product type `X × Y`.
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (p : PullbackObj f g) : X × Y :=
  p

/-- The explicit pullback cone on `PullbackObj f g`.
This is bundled with the `IsLimit` data as `pullbackLimitCone f g`.
-/
/-
**CategoryTheory.Limits.Types.pullbackCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Limits.Types`。
形式化陈述：pullbackCone : Limits.PullbackCone f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit pullback cone on `PullbackObj f g`.
This is bundled with the `IsLimit` data as `pullbackLimitCone f g`.
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (↾fun p : PullbackObj f g => p.1.1)
    (↾fun p => p.1.2) (by ext p; exact p.2)

/-- The explicit pullback in the category of types, bundled up as a `LimitCone`
for given `f` and `g`.
-/
@[simps]
/-
**CategoryTheory.Limits.Types.pullbackLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) 
where cone
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit pullback in the category of types, bundled up as a `LimitCone`
for given `f` and `g`.
-/
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  cone := pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s => ↾fun x => ⟨⟨s.fst x, s.snd x⟩, congr_hom s.condition x⟩)
      (by aesop) (by aesop) fun _ _ w =>
      ConcreteCategory.ext <| TypeCat.Fun.ext <| funext fun x => Subtype.ext <|
        Prod.ext (congr_hom (w WalkingCospan.left) x) (congr_hom (w WalkingCospan.right) x)

end Types

namespace PullbackCone

variable {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : PullbackCone f g}

namespace IsLimit

variable (hc : IsLimit c)

/-- A limit pullback cone in the category of types identifies to the explicit pullback. -/
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：{X Y S : Type v} →   {f : X ⟶ S} →     {g : Y ⟶ S} →       {c : CategoryTh
eory.Limits.PullbackCone f g} →         CategoryTheory.Limits.IsLimit c → c.pt ≃
 CategoryTheory.Limits.Types.PullbackObj f g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A limit pullback cone in the category of types identifies to the explicit pullba
ck.
-/
noncomputable def equivPullbackObj : c.pt ≃ Types.PullbackObj f g :=
  (IsLimit.conePointUniqueUpToIso hc (Types.pullbackLimitCone f g).isLimit).toEquiv

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_apply_fst** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pull
backCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : c.pt),   (↑((Categor
yTheory.Limits.PullbackCone.IsLimit.equivPullbackObj hc) x)).1 =     (CategoryTh
eory.ConcreteCategory.hom c.fst) x
参数：hc : CategoryTheory.Limits.IsLimit c；x : c.pt；↑((CategoryTheory.Limits.Pullba
ckCone.IsLimit.equivPullbackObj hc) x)；CategoryTheory.ConcreteCategory.hom c.fst
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
lemma equivPullbackObj_apply_fst (x : c.pt) : (equivPullbackObj hc x).1.1 = c.fst x :=
  (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .left)) x

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_apply_snd** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pull
backCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : c.pt),   (↑((Categor
yTheory.Limits.PullbackCone.IsLimit.equivPullbackObj hc) x)).2 =     (CategoryTh
eory.ConcreteCategory.hom c.snd) x
参数：hc : CategoryTheory.Limits.IsLimit c；x : c.pt；↑((CategoryTheory.Limits.Pullba
ckCone.IsLimit.equivPullbackObj hc) x)；CategoryTheory.ConcreteCategory.hom c.snd
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
lemma equivPullbackObj_apply_snd (x : c.pt) : (equivPullbackObj hc x).1.2 = c.snd x :=
  (congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp hc
    (Types.pullbackLimitCone f g).isLimit .right)) x

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pull
backCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : CategoryTheory.Limit
s.Types.PullbackObj f g),   (CategoryTheory.ConcreteCategory.hom c.fst)       ((
CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj hc).symm x) =     (↑
x).1
参数：hc : CategoryTheory.Limits.IsLimit c；x : CategoryTheory.Limits.Types.Pullback
Obj f g；CategoryTheory.ConcreteCategory.hom c.fst；(CategoryTheory.Limits.Pullbac
kCone.IsLimit.equivPullbackObj hc).symm x；↑x。
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
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_apply_fst`：∀
 {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.PullbackCon
e f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : c.pt),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivPullbackObj_symm_apply_fst (x : Types.PullbackObj f g) :
    c.fst ((equivPullbackObj hc).symm x) = x.1.1 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pull
backCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : CategoryTheory.Limit
s.Types.PullbackObj f g),   (CategoryTheory.ConcreteCategory.hom c.snd)       ((
CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj hc).symm x) =     (↑
x).2
参数：hc : CategoryTheory.Limits.IsLimit c；x : CategoryTheory.Limits.Types.Pullback
Obj f g；CategoryTheory.ConcreteCategory.hom c.snd；(CategoryTheory.Limits.Pullbac
kCone.IsLimit.equivPullbackObj hc).symm x；↑x。
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
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_apply_snd`：∀
 {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.PullbackCon
e f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : c.pt),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivPullbackObj_symm_apply_snd (x : Types.PullbackObj f g) :
    c.snd ((equivPullbackObj hc).symm x) = x.1.2 := by
  obtain ⟨x, rfl⟩ := (equivPullbackObj hc).surjective x
  simp

include hc in
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.type_ext** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pull
backCone f g}   (hc : CategoryTheory.Limits.IsLimit c) {x y : c.pt},   (Category
Theory.ConcreteCategory.hom c.fst) x = (CategoryTheory.ConcreteCategory.hom c.fs
t) y →     (CategoryTheory.ConcreteCategory.hom c.snd) x = (CategoryTheory.Concr
eteCategory.hom c.snd) y → x = y
参数：hc : CategoryTheory.Limits.IsLimit c；CategoryTheory.ConcreteCategory.hom c.fs
t；CategoryTheory.ConcreteCategory.hom c.fst；CategoryTheory.ConcreteCategory.hom 
c.snd；CategoryTheory.ConcreteCategory.hom c.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
lemma type_ext {x y : c.pt} (h₁ : c.fst x = c.fst y) (h₂ : c.snd x = c.snd y) : x = y :=
  (equivPullbackObj hc).injective (by ext <;> assumption)

end IsLimit

variable (c)

/-- Given `c : PullbackCone f g` in the category of types, this is
the canonical map `c.pt → Types.PullbackObj f g`. -/
@[simps coe_fst coe_snd]
/-
**CategoryTheory.Limits.PullbackCone.toPullbackObj** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：{X Y S : Type v} →   {f : X ⟶ S} →     {g : Y ⟶ S} → (c : CategoryTheory.L
imits.PullbackCone f g) → c.pt → CategoryTheory.Limits.Types.PullbackObj f g
参数：c : CategoryTheory.Limits.PullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `c : PullbackCone f g` in the category of types, this is
the canonical map `c.pt → Types.PullbackObj f g`.
-/
def toPullbackObj (x : c.pt) : Types.PullbackObj f g :=
  ⟨⟨c.fst x, c.snd x⟩, congr_hom c.condition x⟩

/-- A pullback cone `c` in the category of types is limit iff the
map `c.toPullbackObj : c.pt → Types.PullbackObj f g` is a bijection. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitEquivBijective** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：{X Y S : Type v} →   {f : X ⟶ S} →     {g : Y ⟶ S} →       (c : CategoryTh
eory.Limits.PullbackCone f g) →         CategoryTheory.Limits.IsLimit c ≃ Functi
on.Bijective c.toPullbackObj
参数：c : CategoryTheory.Limits.PullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pullback cone `c` in the category of types is limit iff the
map `c.toPullbackObj : c.pt → Types.PullbackObj f g` is a bijection.
-/
noncomputable def isLimitEquivBijective :
    IsLimit c ≃ Function.Bijective c.toPullbackObj where
  toFun h := (IsLimit.equivPullbackObj h).bijective
  invFun h := IsLimit.ofIsoLimit (Types.pullbackLimitCone f g).isLimit
    (Iso.symm (PullbackCone.ext (Equiv.ofBijective _ h).toIso))
  left_inv _ := Subsingleton.elim _ _

end PullbackCone

namespace Types

section Pullback

open CategoryTheory.Limits.WalkingCospan

variable {W X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The pullback given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback object given by `PullbackObj`.
-/
/-
**CategoryTheory.Limits.Types.pullbackIsoPullback** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Types`。
形式化陈述：{X Y Z : Type u} →   (f : X ⟶ Z) → (g : Y ⟶ Z) → CategoryTheory.Limits.pul
lback f g ≅ CategoryTheory.Limits.Types.PullbackObj f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback object given by `PullbackObj`.
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (PullbackCone.IsLimit.equivPullbackObj (pullbackIsPullback f g)).toIso

@[simp]
/-
**CategoryTheory.Limits.Types.pullbackIsoPullback_hom_fst** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Types`。
形式化陈述：∀ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) (p : CategoryTheory.Limits.pull
back f g),   (↑((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.Type
s.pullbackIsoPullback f g).hom) p)).1 =     (CategoryTheory.ConcreteCategory.hom
 (CategoryTheory.Limits.pullback.fst f g)) p
参数：f : X ⟶ Z；g : Y ⟶ Z；p : CategoryTheory.Limits.pullback f g；↑((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.Limits.Types.pullbackIsoPullback f g).hom) 
p)；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.pullback.fst f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_apply_fst`：∀
 {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.PullbackCon
e f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : c.pt),…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem pullbackIsoPullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).fst = (pullback.fst f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst (pullbackIsPullback f g) p

@[simp]
/-
**CategoryTheory.Limits.Types.pullbackIsoPullback_hom_snd** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Types`。
形式化陈述：∀ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) (p : CategoryTheory.Limits.pull
back f g),   (↑((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.Type
s.pullbackIsoPullback f g).hom) p)).2 =     (CategoryTheory.ConcreteCategory.hom
 (CategoryTheory.Limits.pullback.snd f g)) p
参数：f : X ⟶ Z；g : Y ⟶ Z；p : CategoryTheory.Limits.pullback f g；↑((CategoryTheory.
ConcreteCategory.hom (CategoryTheory.Limits.Types.pullbackIsoPullback f g).hom) 
p)；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.pullback.snd f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_apply_snd`：∀
 {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.PullbackCon
e f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : c.pt),…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem pullbackIsoPullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).snd = (pullback.snd f g) p :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd (pullbackIsPullback f g) p

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.pullbackIsoPullback_inv_fst** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Types`。
形式化陈述：∀ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.CategoryStruc
t.comp (CategoryTheory.Limits.Types.pullbackIsoPullback f g).inv       (Category
Theory.Limits.pullback.fst f g) =     TypeCat.ofHom fun p => (↑p).1
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.Types.pullbackIsoPullback f g；Categ
oryTheory.Limits.pullback.fst f g；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_symm_apply_f
st`：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pullba
ckCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : Catego…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem pullbackIsoPullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst _ _ =
      ↾fun p => (p.1 : X × Y).fst := by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackIsPullback f g) _

@[elementwise (attr := simp)]
/-
**CategoryTheory.Limits.Types.pullbackIsoPullback_inv_snd** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.Types`。
形式化陈述：∀ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.CategoryStruc
t.comp (CategoryTheory.Limits.Types.pullbackIsoPullback f g).inv       (Category
Theory.Limits.pullback.snd f g) =     TypeCat.ofHom fun p => (↑p).2
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.Types.pullbackIsoPullback f g；Categ
oryTheory.Limits.pullback.snd f g；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_symm_apply_s
nd`：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pullba
ckCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : Catego…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem pullbackIsoPullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd _ _ =
      ↾fun p => (p.1 : X × Y).snd := by
  ext
  exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackIsPullback f g) _

end Pullback

end Types

end CategoryTheory.Limits


namespace CategoryTheory.Limits.Types

variable {P X Y Z : Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-
**CategoryTheory.Limits.Types.range_fst_of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Types`。
形式化陈述：∀ {P X Y Z : Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}, 
  CategoryTheory.IsPullback fst snd f g →     Set.range ⇑(CategoryTheory.Concret
eCategory.hom fst) =       ⇑(CategoryTheory.ConcreteCategory.hom f) ⁻¹' Set.rang
e ⇑(CategoryTheory.ConcreteCategory.hom g)
参数：CategoryTheory.ConcreteCategory.hom fst；CategoryTheory.ConcreteCategory.hom f
；CategoryTheory.ConcreteCategory.hom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `CategoryTheory.surjective_of_epi`：surjective_of_epi {X Y : Type u} (f : 
X ⟶ Y) [hf : Epi f] : Function.Surjective f
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_fst_of_isPullback (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  let e := h.isoPullback ≪≫ Types.pullbackIsoPullback f g
  have : fst = _root_.Prod.fst ∘ Subtype.val ∘ e.hom := by
    ext p
    suffices fst p = pullback.fst f g (h.isoPullback.hom p) by simpa
    rw [← comp_apply h.isoPullback.hom (pullback.fst f g), IsPullback.isoPullback_hom_fst]
  rw [this, Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr (surjective_of_epi e.hom)]
  ext
  simp [eq_comm]
/-
**CategoryTheory.Limits.Types.range_snd_of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Types`。
形式化陈述：∀ {P X Y Z : Type u} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}, 
  CategoryTheory.IsPullback fst snd f g →     Set.range ⇑(CategoryTheory.Concret
eCategory.hom snd) =       ⇑(CategoryTheory.ConcreteCategory.hom g) ⁻¹' Set.rang
e ⇑(CategoryTheory.ConcreteCategory.hom f)
参数：CategoryTheory.ConcreteCategory.hom snd；CategoryTheory.ConcreteCategory.hom g
；CategoryTheory.ConcreteCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.range_fst_of_isPullback`：∀ {P X Y Z : Type u
} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   CategoryTheory.IsPullba
ck fst snd f g →     Set.range ⇑(Category…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
lemma range_snd_of_isPullback (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  rw [range_fst_of_isPullback (IsPullback.flip h)]

variable (f g)

@[simp]
/-
**CategoryTheory.Limits.Types.range_pullbackFst** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：∀ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z),   Set.range ⇑(CategoryTheory.C
oncreteCategory.hom (CategoryTheory.Limits.pullback.fst f g)) =     ⇑(CategoryTh
eory.ConcreteCategory.hom f) ⁻¹' Set.range ⇑(CategoryTheory.ConcreteCategory.hom
 g)
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limit
s.pullback.fst f g)；CategoryTheory.ConcreteCategory.hom f；CategoryTheory.Concret
eCategory.hom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.range_fst_of_isPullback`：∀ {P X Y Z : Type u
} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   CategoryTheory.IsPullba
ck fst snd f g →     Set.range ⇑(Category…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma range_pullbackFst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g :=
  range_fst_of_isPullback (.of_hasPullback f g)

@[simp]
/-
**CategoryTheory.Limits.Types.range_pullbackSnd** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：∀ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z),   Set.range ⇑(CategoryTheory.C
oncreteCategory.hom (CategoryTheory.Limits.pullback.snd f g)) =     ⇑(CategoryTh
eory.ConcreteCategory.hom g) ⁻¹' Set.range ⇑(CategoryTheory.ConcreteCategory.hom
 f)
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limit
s.pullback.snd f g)；CategoryTheory.ConcreteCategory.hom g；CategoryTheory.Concret
eCategory.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.range_snd_of_isPullback`：∀ {P X Y Z : Type u
} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   CategoryTheory.IsPullba
ck fst snd f g →     Set.range ⇑(Category…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma range_pullbackSnd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f :=
  range_snd_of_isPullback (.of_hasPullback f g)

section

variable {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄}
  {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.Types.ext_of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：∀ {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄} {l : X₁ ⟶ X₃} {b : X₃
 ⟶ X₄},   CategoryTheory.IsPullback t l r b →     ∀ {x₁ y₁ : X₁},       (Categor
yTheory.ConcreteCategory.hom t) x₁ = (CategoryTheory.ConcreteCategory.hom t) y₁ 
→         (CategoryTheory.ConcreteCategory.hom l) x₁ = (CategoryTheory.ConcreteC
ategory.hom l) y₁ → x₁ = y₁
参数：CategoryTheory.ConcreteCategory.hom t；CategoryTheory.ConcreteCategory.hom t；C
ategoryTheory.ConcreteCategory.hom l；CategoryTheory.ConcreteCategory.hom l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
lemma ext_of_isPullback (h : IsPullback t l r b) {x₁ y₁ : X₁}
    (h₁ : t x₁ = t y₁) (h₂ : l x₁ = l y₁) : x₁ = y₁ :=
  (h.isLimit.conePointUniqueUpToIso (Types.pullbackLimitCone _ _).isLimit).toEquiv.injective
    (by dsimp; ext <;> assumption)
/-
**CategoryTheory.Limits.Types.exists_of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.Types`。
形式化陈述：∀ {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄} {l : X₁ ⟶ X₃} {b : X₃
 ⟶ X₄},   CategoryTheory.IsPullback t l r b →     ∀ (x₂ : X₂) (x₃ : X₃),       (
CategoryTheory.ConcreteCategory.hom r) x₂ = (CategoryTheory.ConcreteCategory.hom
 b) x₃ →         ∃ x₁, (CategoryTheory.ConcreteCategory.hom t) x₁ = x₂ ∧ (Catego
ryTheory.ConcreteCategory.hom l) x₁ = x₃
参数：x₂ : X₂；x₃ : X₃；CategoryTheory.ConcreteCategory.hom r；CategoryTheory.Concrete
Category.hom b；CategoryTheory.ConcreteCategory.hom t；CategoryTheory.ConcreteCate
gory.hom l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma exists_of_isPullback (h : IsPullback t l r b)
    (x₂ : X₂) (x₃ : X₃) (hx : r x₂ = b x₃) :
    ∃ x₁, t x₁ = x₂ ∧ l x₁ = x₃ := by
  obtain ⟨x₁, hx₁⟩ :=
    (PullbackCone.IsLimit.equivPullbackObj h.isLimit).surjective ⟨⟨x₂, x₃⟩, hx⟩
  rw [Subtype.ext_iff] at hx₁
  exact ⟨x₁, congr_arg _root_.Prod.fst hx₁,
    congr_arg _root_.Prod.snd hx₁⟩

set_option backward.isDefEq.respectTransparency false in
variable (t l r b) in
/-
**CategoryTheory.Limits.Types.isPullback_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Types`。
形式化陈述：∀ {X₁ X₂ X₃ X₄ : Type u} (t : X₁ ⟶ X₂) (r : X₂ ⟶ X₄) (l : X₁ ⟶ X₃) (b : X₃
 ⟶ X₄),   CategoryTheory.IsPullback t l r b ↔     CategoryTheory.CategoryStruct.
comp t r = CategoryTheory.CategoryStruct.comp l b ∧       (∀ (x₁ y₁ : (fun X => 
X) X₁),           (CategoryTheory.ConcreteCategory.hom t) x₁ = (CategoryTheory.C
oncreteCategory.hom t) y₁ ∧               (CategoryTheory.ConcreteCategory.hom l
) x₁ = (CategoryTheory.ConcreteCategory.hom l) y₁ →             x₁ = y₁) ∧      
   ∀ (x₂ : (fun X => X) X₂) (x₃ : (fun X => X) X₃),           (CategoryTheory.Co
ncreteCategory.hom r) x₂ = (CategoryTheory.ConcreteCategory.hom b) x₃ →         
    ∃ x₁, (CategoryTheory.ConcreteCategory.hom t) x₁ = x₂ ∧ (CategoryTheory.Conc
reteCategory.hom l) x₁ = x₃
参数：t : X₁ ⟶ X₂；r : X₂ ⟶ X₄；l : X₁ ⟶ X₃；b : X₃ ⟶ X₄；∀ (x₁ y₁ : (fun X => X) X₁), 
          (CategoryTheory.ConcreteCategory.hom t) x₁ = (CategoryTheory.ConcreteC
ategory.hom t) y₁ ∧               (CategoryTheory.ConcreteCategory.hom l) x₁ = (
CategoryTheory.ConcreteCategory.hom l) y₁ →             x₁ = y₁；x₂ : (fun X => X
) X₂；x₃ : (fun X => X) X₃；CategoryTheory.ConcreteCategory.hom r；CategoryTheory.C
oncreteCategory.hom b；CategoryTheory.ConcreteCategory.hom t；CategoryTheory.Concr
eteCategory.hom l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.Types.ext_of_isPullback`：∀ {X₁ X₂ X₃ X₄ : Type u} 
{t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄} {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄},   CategoryTheory.IsPull
back t l r b →     ∀ {x₁ y₁ : X₁}, …
· 使用定理 `CategoryTheory.Limits.Types.exists_of_isPullback`：∀ {X₁ X₂ X₃ X₄ : Type 
u} {t : X₁ ⟶ X₂} {r : X₂ ⟶ X₄} {l : X₁ ⟶ X₃} {b : X₃ ⟶ X₄},   CategoryTheory.IsP
ullback t l r b →     ∀ (x₂ : X₂) (x₃ …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isPullback_iff :
  IsPullback t l r b ↔ t ≫ r = l ≫ b ∧
    (∀ x₁ y₁, t x₁ = t y₁ ∧ l x₁ = l y₁ → x₁ = y₁) ∧
    ∀ x₂ x₃, r x₂ = b x₃ → ∃ x₁, t x₁ = x₂ ∧ l x₁ = x₃ := by
  constructor
  · intro h
    exact ⟨h.w, fun x₁ y₁ ⟨h₁, h₂⟩ ↦ ext_of_isPullback h h₁ h₂, exists_of_isPullback h⟩
  · rintro ⟨w, h₁, h₂⟩
    let φ : X₁ ⟶ PullbackObj r b := ↾fun x₁ ↦ ⟨⟨t x₁, l x₁⟩, congr_hom w x₁⟩
    have hφ : IsIso φ := by
      rw [isIso_iff_bijective]
      constructor
      · intro _ _ h
        simp [φ] at h
        grind
      · intro x
        obtain ⟨a, ha⟩ := h₂ x.1.1 x.1.2 (by grind)
        cat_disch
    exact ⟨⟨w⟩, ⟨IsLimit.ofIsoLimit ((Types.pullbackLimitCone r b).isLimit)
      (PullbackCone.ext (asIso φ)).symm⟩⟩

end

end CategoryTheory.Limits.Types

