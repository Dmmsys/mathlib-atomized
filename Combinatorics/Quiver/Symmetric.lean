/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Antoine Labelle, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Combinatorics.Quiver.Push

/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `Symmetrify V` adds formal inverses to each arrow of `V`.
* `HasReverse` is the class of quivers where each arrow has an assigned formal inverse.
* `HasInvolutiveReverse` extends `HasReverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `Prefunctor.PreserveReverse` is the class of prefunctors mapping reverses to reverses.
* `Symmetrify.of`, `Symmetrify.lift`, and the associated lemmas witness the universal property
  of `Symmetrify`.
-/

@[expose] public section

universe v u w v'

namespace Quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
-/
/-
**Quiver.Symmetrify** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：Symmetrify (V : Type*)
参数：V : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for the symmetrized quiver (with an arrow both ways for each orig
inal arrow).
-/
def Symmetrify (V : Type*) := V
/-
**Quiver.symmetrifyQuiver** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
形式化陈述：symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V)
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V ↦ (a ⟶ b) ⊕ (b ⟶ a)⟩

variable (U V W : Type*) [Quiver.{u} U] [Quiver.{v} V] [Quiver.{w} W]

/-- A quiver `HasReverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`. -/
/-
**Quiver.HasReverse** 是 Mathlib 中的一个归纳类型，位于命名空间 `Quiver`。
形式化陈述：(V : Type u_2) → [Quiver V] → Type (max u_2 v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quiver `HasReverse` if we can reverse an arrow `p` from `a` to `b` to get an a
rrow
    `p.reverse` from `b` to `a`.
-/
class HasReverse where
  /-- the map which sends an arrow to its reverse -/
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

/-- Reverse the direction of an arrow. -/
/-
**Quiver.reverse** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：reverse {V} [Quiver.{v} V] [HasReverse V] {a b : V} : (a ⟶ b) -> (b ⟶ a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reverse the direction of an arrow.
-/
def reverse {V} [Quiver.{v} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  HasReverse.reverse'

/-- A quiver `HasInvolutiveReverse` if reversing twice is the identity. -/
/-
**Quiver.HasInvolutiveReverse** 是 Mathlib 中的一个归纳类型，位于命名空间 `Quiver`。
形式化陈述：(V : Type u_2) → [Quiver V] → Type (max u_2 v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quiver `HasInvolutiveReverse` if reversing twice is the identity.
-/
class HasInvolutiveReverse extends HasReverse V where
  /-- `reverse` is involutive -/
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f

variable {U V W}

@[simp]
/-
**Quiver.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) : rever
se (reverse f) = f
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.HasInvolutiveReverse.inv'`：∀ {V : Type u_2} {inst : Quiver V} [se
lf : Quiver.HasInvolutiveReverse V] {a b : V} (f : a ⟶ b),   Quiver.reverse (Qui
ver.reverse f) = f
-/
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'

@[simp]
/-
**Quiver.reverse_inj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：reverse_inj [h : HasInvolutiveReverse V] {a b : V} (f g : a ⟶ b) : reverse
 f = reverse g ↔ f = g
参数：f g : a ⟶ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.reverse_reverse`：reverse_reverse [h : HasInvolutiveReverse V] {a 
b : V} (f : a ⟶ b) : reverse (reverse f) = f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem reverse_inj [h : HasInvolutiveReverse V] {a b : V}
    (f g : a ⟶ b) : reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr
/-
**Quiver.eq_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：eq_reverse_iff [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) (g : b ⟶
 a) : f = reverse g ↔ reverse f = g
参数：f : a ⟶ b；g : b ⟶ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.reverse_inj`：reverse_inj [h : HasInvolutiveReverse V] {a b : V} (
f g : a ⟶ b) : reverse f = reverse g ↔ f = g
· 使用定理 `Quiver.reverse_reverse`：reverse_reverse [h : HasInvolutiveReverse V] {a 
b : V} (f : a ⟶ b) : reverse (reverse f) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_reverse_iff [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
    (g : b ⟶ a) : f = reverse g ↔ reverse f = g := by
  rw [← reverse_inj, reverse_reverse]

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

/-- A prefunctor preserving reversal of arrows -/
/-
**Quiver._root_.Prefunctor.MapReverse** 是 Mathlib 中的一个类，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor preserving reversal of arrows
-/
class _root_.Prefunctor.MapReverse (φ : U ⥤q V) : Prop where
  /-- The image of a reverse is the reverse of the image. -/
  map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)

@[simp]
/-
**Quiver._root_.Prefunctor.map_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse]
    {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e

set_option backward.isDefEq.respectTransparency false in
/-
**Quiver._root_.Prefunctor.mapReverseComp** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prefunctor.mapReverseComp
    (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse where
  map_reverse' e := by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']
/-
**Quiver._root_.Prefunctor.mapReverseId** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prefunctor.mapReverseId :
    (Prefunctor.id U).MapReverse where
  map_reverse' _ := rfl

end MapReverse

/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasReverse (Symmetrify V) :=
  ⟨fun e => e.swap⟩
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    HasInvolutiveReverse
      (Symmetrify V) where
  toHasReverse := ⟨fun e ↦ e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e

@[simp]
/-
**Quiver.symmetrify_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap
参数：e : a ⟶ b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap :=
  rfl

section Paths

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
/-
**Quiver.Hom.toPos** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u_2} → [inst : Quiver V] → {X Y : V} → (X ⟶ Y) → (X ⟶ Y)
参数：X ⟶ Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V`
-/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
/-
**Quiver.Hom.toNeg** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u_2} → [inst : Quiver V] → {X Y : V} → (X ⟶ Y) → (Y ⟶ X)
参数：X ⟶ Y；Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V`
-/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f

/-- Reverse the direction of a path. -/
@[simp]
/-
**Quiver.Path.reverse** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u_2} → [inst : Quiver V] → [Quiver.HasReverse V] → {a b : V} → Q
uiver.Path a b → Quiver.Path b a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reverse the direction of a path.
-/
def Path.reverse [HasReverse V] {a : V} : ∀ {b}, Path a b → Path b a
  | _, Path.nil => Path.nil
  | _, Path.cons p e => (Quiver.reverse e).toPath.comp p.reverse

@[simp]
/-
**Quiver.Path.reverse_toPath** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Quiver.HasReverse V] {a b : V
} (f : a ⟶ b),   f.toPath.reverse = (Quiver.reverse f).toPath
参数：f : a ⟶ b；Quiver.reverse f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (Quiver.reverse f).toPath :=
  rfl

@[simp]
/-
**Quiver.Path.reverse_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Quiver.HasReverse V] {a b c :
 V} (p : Quiver.Path a b)   (q : Quiver.Path b c), (p.comp q).reverse = q.revers
e.comp p.reverse
参数：p : Quiver.Path a b；q : Quiver.Path b c；p.comp q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.nil_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Qu
iver.Path a b), Quiver.Path.nil.comp p = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Quiver.Path.reverse.eq_2`：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Q
uiver.HasReverse V] {a : V} (x b : V) (p : Quiver.Path a b) (e : b ⟶ x),   (p.co
ns e).reverse …
· 使用定理 `Quiver.Path.comp_assoc`：∀ {V : Type u} [inst : Quiver V] {a b c d : V} (
p : Quiver.Path a b) (q : Quiver.Path b c) (r : Quiver.Path c d),   (p.comp q).c
omp r = p.co…
-/
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction q with
  | nil => simp
  | cons _ _ h => simp [h]

@[simp]
/-
**Quiver.Path.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V] [h : Quiver.HasInvolutiveReverse V] {a 
b : V} (p : Quiver.Path a b),   p.reverse.reverse = p
参数：p : Quiver.Path a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.reverse.eq_1`：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Q
uiver.HasReverse V] {a : V}, Quiver.Path.nil.reverse = Quiver.Path.nil
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Quiver.Path.reverse.eq_2`：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Q
uiver.HasReverse V] {a : V} (x b : V) (p : Quiver.Path a b) (e : b ⟶ x),   (p.co
ns e).reverse …
· 使用定理 `Quiver.Path.reverse_comp`：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Q
uiver.HasReverse V] {a b c : V} (p : Quiver.Path a b)   (q : Quiver.Path b c), (
p.comp q).reve…
· 使用定理 `Quiver.Path.reverse_toPath`：∀ {V : Type u_2} [inst : Quiver V] [inst_1 :
 Quiver.HasReverse V] {a b : V} (f : a ⟶ b),   f.toPath.reverse = (Quiver.revers
e f).toPath
· 使用定理 `Quiver.reverse_reverse`：reverse_reverse [h : HasInvolutiveReverse V] {a 
b : V} (f : a ⟶ b) : reverse (reverse f) = f
-/
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction p with
  | nil => simp
  | cons _ _ h =>
    rw [Path.reverse, Path.reverse_comp, h, Path.reverse_toPath, Quiver.reverse_reverse]
    rfl

end Paths

namespace Symmetrify

/-- The inclusion of a quiver in its symmetrification -/
@[simps]
/-
**Quiver.Symmetrify.of** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Symmetrify`。
形式化陈述：of : Prefunctor V (Symmetrify V) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a quiver in its symmetrification
-/
def of : Prefunctor V (Symmetrify V) where
  obj := id
  map := Sum.inl

variable {V' : Type*} [Quiver.{v'} V']

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `Symmetrify V` to `V'` -/
/-
**Quiver.Symmetrify.lift** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Symmetrify`。
形式化陈述：lift [HasReverse V'] (φ : Prefunctor V V') : Prefunctor (Symmetrify V) V' 
where obj
参数：φ : Prefunctor V V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted t
o one from
    `Symmetrify V` to `V'`
-/
def lift [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)
/-
**Quiver.Symmetrify.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Symmetrify`。
形式化陈述：lift_spec [HasReverse V'] (φ : Prefunctor V V') : Symmetrify.of.comp (Symm
etrify.lift φ) = φ
参数：φ : Prefunctor V V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.ext`：ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{
v₂} W] {F G : Prefunctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : for
all …
-/
theorem lift_spec [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl
/-
**Quiver.Symmetrify.lift_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Symmetrify`。
形式化陈述：lift_reverse [h : HasInvolutiveReverse V'] (φ : Prefunctor V V') {X Y : Sy
mmetrify V} (f : X ⟶ Y) : (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.re
verse ((Symmetrify.lift φ).map f)
参数：φ : Prefunctor V V'；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.reverse_reverse`：reverse_reverse [h : HasInvolutiveReverse V] {a 
b : V} (f : a ⟶ b) : reverse (reverse f) = f
-/
theorem lift_reverse [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
/-
**Quiver.Symmetrify.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Symmetrify`。
形式化陈述：lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (
of ⋙q Φ) = φ) (hΦinv : forall {X Y : Symmetrify V} (f : X ⟶ Y), Φ.map (Quiver.re
verse f) = Quiver.reverse (Φ.map f)) : Φ = Symmetrify.lift φ
参数：φ : V ⥤q V'；Φ : Symmetrify V ⥤q V'；hΦ : (of ⋙q Φ) = φ；hΦinv : forall {X Y : S
ymmetrify V} (f : X ⟶ Y), Φ.map (Quiver.reverse f) = Quiver.reverse (Φ.map f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.ext`：ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{
v₂} W] {F G : Prefunctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : for
all …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`lift φ` is the only prefunctor extending `φ` and preserving reverses.
-/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
    (hΦinv : ∀ {X Y : Symmetrify V} (f : X ⟶ Y),
      Φ.map (Quiver.reverse f) = Quiver.reverse (Φ.map f)) :
    Φ = Symmetrify.lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · exact hΦinv (Sum.inl _)

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
/-
**Quiver.Symmetrify._root_.Prefunctor.symmetrify** 是 Mathlib 中的一个定义，位于命名空间 `Quiv
er.Symmetrify`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prefunctor canonically defines a prefunctor of the symmetrifications.
-/
def _root_.Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V where
  obj := φ.obj
  map := Sum.map φ.map φ.map
/-
**Quiver.Symmetrify._root_.Prefunctor.symmetrify_mapReverse** 是 Mathlib 中的一个实例，位
于命名空间 `Quiver.Symmetrify`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prefunctor.symmetrify_mapReverse (φ : U ⥤q V) :
    Prefunctor.MapReverse φ.symmetrify :=
  ⟨fun e => by cases e <;> rfl⟩

end Symmetrify

namespace Push

variable {V' : Type*} (σ : V → V')

/-
**Quiver.Push.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Push`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasReverse V] : HasReverse (Quiver.Push σ) where
  reverse' := fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
/-
**Quiver.Push.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Push`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : HasInvolutiveReverse V] :
    HasInvolutiveReverse (Push σ) where
  reverse' := fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'
/-
**Quiver.Push.of_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Push`。
形式化陈述：of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) : (reverse <| (P
ush.of σ).map f) = (Push.of σ).map (reverse f)
参数：X Y : V；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Quiver.Push.ofMapReverse** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Push`。
形式化陈述：ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩

end Push

end Quiver

