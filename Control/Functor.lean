/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Set.Defs

import Mathlib.Tactic.Attr.Register

/-!
# Functors

This module provides additional lemmas, definitions, and instances for `Functor`s.

## Main definitions

* `Functor.Const α` is the functor that sends all types to `α`.
* `Functor.AddConst α` is `Functor.Const α` but for when `α` has an additive structure.
* `Functor.Comp F G` for functors `F` and `G` is the functor composition of `F` and `G`.
* `Liftp` and `Liftr` respectively lift predicates and relations on a type `α`
  to `F α`.  Terms of `F α` are considered to, in some sense, contain values of type `α`.

## Tags

functor, applicative
-/

@[expose] public section

universe u v w

section Functor

variable {F : Type u → Type v}
variable {α β γ : Type u}
variable [Functor F] [LawfulFunctor F]

/-
**Functor.map_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Functor.map_id : (id <$> ·) = (id : F α -> F α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
-/
theorem Functor.map_id : (id <$> ·) = (id : F α → F α) := funext id_map
/-
**Functor.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Functor.map_comp_map (f : α -> β) (g : β -> γ) : ((g <$> ·) ∘ (f <$> ·) : 
F α -> F γ) = ((g ∘ f) <$> ·)
参数：f : α -> β；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulFunctor.comp_map`：∀ {f : Type u → Type v} {inst : Functor f} [self
 : LawfulFunctor f] {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α),   (h ∘ g
) <$> x = h …
-/
theorem Functor.map_comp_map (f : α → β) (g : β → γ) :
    ((g <$> ·) ∘ (f <$> ·) : F α → F γ) = ((g ∘ f) <$> ·) :=
  funext fun _ => (comp_map _ _ _).symm

set_option linter.overlappingInstances false in
/-
**Functor.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Functor.ext {F} : forall {F1 : Functor F} {F2 : Functor F} [@LawfulFunctor
 F F1] [@LawfulFunctor F F2], (forall (α β) (f : α -> β) (x : F α), @Functor.map
 _ F1 _ _ f x = @Functor.map _ F2 _ _ f x) -> F1 = F2 | ⟨m, mc⟩, ⟨m', mc'⟩, H1, 
H2, H => by cases show @m = @m' by funext α β f x; apply H congr funext α β have
 E1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulFunctor.map_const`：∀ {f : Type u → Type v} {inst : Functor f} [sel
f : LawfulFunctor f] {α β : Type u},   Functor.mapConst = Functor.map ∘ Function
.const β
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Functor.ext {F} :
    ∀ {F1 : Functor F} {F2 : Functor F} [@LawfulFunctor F F1] [@LawfulFunctor F F2],
    (∀ (α β) (f : α → β) (x : F α), @Functor.map _ F1 _ _ f x = @Functor.map _ F2 _ _ f x) →
    F1 = F2
  | ⟨m, mc⟩, ⟨m', mc'⟩, H1, H2, H => by
    cases show @m = @m' by funext α β f x; apply H
    congr
    funext α β
    have E1 := @map_const _ ⟨@m, @mc⟩ H1
    have E2 := @map_const _ ⟨@m, @mc'⟩ H2
    exact E1.trans E2.symm

end Functor

namespace Functor

/-- `Const α` is the constant functor, mapping every type to `α`. When
`α` has a monoid structure, `Const α` has an `Applicative` instance.
(If `α` has an additive monoid structure, see `Functor.AddConst`.) -/
@[nolint unusedArguments]
/-
**Functor.Const** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：Const (α : Type*) (_β : Type*)
参数：α : Type*；_β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Const α` is the constant functor, mapping every type to `α`. When
`α` has a monoid structure, `Const α` has an `Applicative` instance.
(If `α` has an additive monoid structure, see `Functor.AddConst`.)
-/
def Const (α : Type*) (_β : Type*) :=
  α

/-- `Const.mk` is the canonical map `α → Const α β` (the identity), and
it can be used as a pattern to extract this value. -/
@[match_pattern]
/-
**Functor.Const.mk** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Const`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α → Functor.Const α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Const.mk` is the canonical map `α → Const α β` (the identity), and
it can be used as a pattern to extract this value.
-/
def Const.mk {α β} (x : α) : Const α β :=
  x

/-- `Const.mk'` is `Const.mk` but specialized to map `α` to
`Const α PUnit`, where `PUnit` is the terminal object in `Type*`. -/
/-
**Functor.Const.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Const`。
形式化陈述：{α : Type u_1} → α → Functor.Const α PUnit.{u_2 + 1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Const.mk'` is `Const.mk` but specialized to map `α` to
`Const α PUnit`, where `PUnit` is the terminal object in `Type*`.
-/
def Const.mk' {α} (x : α) : Const α PUnit :=
  x

/-- Extract the element of `α` from the `Const` functor. -/
/-
**Functor.Const.run** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Const`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Functor.Const α β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the element of `α` from the `Const` functor.
-/
def Const.run {α β} (x : Const α β) : α :=
  x

namespace Const

/-
**Functor.Const.ext** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Const`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : Functor.Const α β}, x.run = y.run →
 x = y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ext {α β} {x y : Const α β} (h : x.run = y.run) : x = y :=
  h

/-- The map operation of the `Const γ` functor. -/
@[nolint unusedArguments]
/-
**Functor.Const.map** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Const`。
形式化陈述：{γ : Type u_1} → {α : Type u_2} → {β : Type u_3} → (α → β) → Functor.Const
 γ β → Functor.Const γ α
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map operation of the `Const γ` functor.
-/
protected def map {γ α β} (_f : α → β) (x : Const γ β) : Const γ α :=
  x
/-
**Functor.Const.functor** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Const`。
形式化陈述：functor {γ} : Functor (Const γ) where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functor {γ} : Functor (Const γ) where map := @Const.map γ
/-
**Functor.Const.lawfulFunctor** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Const`。
形式化陈述：lawfulFunctor {γ} : LawfulFunctor (Const γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lawfulFunctor {γ} : LawfulFunctor (Const γ) := by constructor <;> intros <;> rfl
/-
**Functor.Const.** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Const`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β} [Inhabited α] : Inhabited (Const α β) :=
  ⟨(default : α)⟩

end Const

/-- `AddConst α` is a synonym for constant functor `Const α`, mapping
every type to `α`. When `α` has an additive monoid structure,
`AddConst α` has an `Applicative` instance. (If `α` has a
multiplicative monoid structure, see `Functor.Const`.) -/
/-
**Functor.AddConst** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：AddConst (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddConst α` is a synonym for constant functor `Const α`, mapping
every type to `α`. When `α` has an additive monoid structure,
`AddConst α` has an `Applicative` instance. (If `α` has a
multiplicative monoid structure, see `Functor.Const`.)
-/
def AddConst (α : Type*) :=
  Const α

/-- `AddConst.mk` is the canonical map `α → AddConst α β`, which is the identity,
where `AddConst α β = Const α β`. It can be used as a pattern to extract this value. -/
@[match_pattern]
/-
**Functor.AddConst.mk** 是 Mathlib 中的一个定义，位于命名空间 `Functor.AddConst`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α → Functor.AddConst α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddConst.mk` is the canonical map `α → AddConst α β`, which is the identity,
where `AddConst α β = Const α β`. It can be used as a pattern to extract this va
lue.
-/
def AddConst.mk {α β} (x : α) : AddConst α β :=
  x

/-- Extract the element of `α` from the constant functor. -/
/-
**Functor.AddConst.run** 是 Mathlib 中的一个定义，位于命名空间 `Functor.AddConst`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Functor.AddConst α β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the element of `α` from the constant functor.
-/
def AddConst.run {α β} : AddConst α β → α :=
  id
/-
**Functor.AddConst.functor** 是 Mathlib 中的一个定义，位于命名空间 `Functor.AddConst`。
形式化陈述：{γ : Type u_1} → Functor (Functor.AddConst γ)
参数：Functor.AddConst γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddConst.functor {γ} : Functor (AddConst γ) :=
  @Const.functor γ
/-
**Functor.AddConst.lawfulFunctor** 是 Mathlib 中的一个定理，位于命名空间 `Functor.AddConst`。
形式化陈述：∀ {γ : Type u_1}, LawfulFunctor (Functor.AddConst γ)
参数：Functor.AddConst γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddConst.lawfulFunctor {γ} : LawfulFunctor (AddConst γ) :=
  @Const.lawfulFunctor γ
/-
**Functor.** 是 Mathlib 中的一个实例，位于命名空间 `Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β} [Inhabited α] : Inhabited (AddConst α β) :=
  ⟨(default : α)⟩

/-- `Functor.Comp` is a wrapper around `Function.Comp` for types.
It prevents Lean's type class resolution mechanism from trying
a `Functor (Comp F id)` when `Functor F` would do. -/
/-
**Functor.Comp** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：Comp (F : Type u -> Type w) (G : Type v -> Type u) (α : Type v) : Type w
参数：F : Type u -> Type w；G : Type v -> Type u；α : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.Comp` is a wrapper around `Function.Comp` for types.
It prevents Lean's type class resolution mechanism from trying
a `Functor (Comp F id)` when `Functor F` would do.
-/
def Comp (F : Type u → Type w) (G : Type v → Type u) (α : Type v) : Type w :=
  F <| G α

/-- Construct a term of `Comp F G α` from a term of `F (G α)`, which is the same type.
Can be used as a pattern to extract a term of `F (G α)`. -/
@[match_pattern]
/-
**Functor.Comp.mk** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Comp`。
形式化陈述：{F : Type u → Type w} → {G : Type v → Type u} → {α : Type v} → F (G α) → F
unctor.Comp F G α
参数：G α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a term of `Comp F G α` from a term of `F (G α)`, which is the same typ
e.
Can be used as a pattern to extract a term of `F (G α)`.
-/
def Comp.mk {F : Type u → Type w} {G : Type v → Type u} {α : Type v} (x : F (G α)) : Comp F G α :=
  x

/-- Extract a term of `F (G α)` from a term of `Comp F G α`, which is the same type. -/
/-
**Functor.Comp.run** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Comp`。
形式化陈述：{F : Type u → Type w} → {G : Type v → Type u} → {α : Type v} → Functor.Com
p F G α → F (G α)
参数：G α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract a term of `F (G α)` from a term of `Comp F G α`, which is the same type.
-/
def Comp.run {F : Type u → Type w} {G : Type v → Type u} {α : Type v} (x : Comp F G α) : F (G α) :=
  x

namespace Comp

variable {F : Type u → Type w} {G : Type v → Type u}

/-
**Functor.Comp.ext** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：∀ {F : Type u → Type w} {G : Type v → Type u} {α : Type v} {x y : Functor.
Comp F G α}, x.run = y.run → x = y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ext {α} {x y : Comp F G α} : x.run = y.run → x = y :=
  id
/-
**Functor.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [Inhabited (F (G α))] : Inhabited (Comp F G α) :=
  ⟨(default : F (G α))⟩

variable [Functor F] [Functor G]

/-- The map operation for the composition `Comp F G` of functors `F` and `G`. -/
/-
**Functor.Comp.map** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Comp`。
形式化陈述：{F : Type u → Type w} →   {G : Type v → Type u} → [Functor F] → [Functor G
] → {α β : Type v} → (α → β) → Functor.Comp F G α → Functor.Comp F G β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map operation for the composition `Comp F G` of functors `F` and `G`.
-/
protected def map {α β : Type v} (h : α → β) : Comp F G α → Comp F G β
  | Comp.mk x => Comp.mk ((h <$> ·) <$> x)
/-
**Functor.Comp.functor** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
形式化陈述：functor : Functor (Comp F G) where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functor : Functor (Comp F G) where map := @Comp.map F G _ _

@[functor_norm]
/-
**Functor.Comp.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：map_mk {α β} (h : α -> β) (x : F (G α)) : h < > Comp.mk x = Comp.mk ((h <$
> ·) <$> x)
参数：h : α -> β；x : F (G α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk {α β} (h : α → β) (x : F (G α)) : h <$> Comp.mk x = Comp.mk ((h <$> ·) <$> x) :=
  rfl

@[simp]
/-
**Functor.Comp.run_map** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：∀ {F : Type u → Type w} {G : Type v → Type u} [inst : Functor F] [inst_1 :
 Functor G] {α β : Type v} (h : α → β)   (x : Functor.Comp F G α), (h <$> x).run
 = (fun x => h <$> x) <$> x.run
参数：h : α → β；x : Functor.Comp F G α；h <$> x；fun x => h <$> x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem run_map {α β} (h : α → β) (x : Comp F G α) :
    (h <$> x).run = (h <$> ·) <$> x.run :=
  rfl

variable [LawfulFunctor F] [LawfulFunctor G]
variable {α β γ : Type v}

set_option backward.isDefEq.respectTransparency false in
/-
**Functor.Comp.id_map** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：∀ {F : Type u → Type w} {G : Type v → Type u} [inst : Functor F] [inst_1 :
 Functor G] [LawfulFunctor F]   [LawfulFunctor G] {α : Type v} (x : Functor.Comp
 F G α), Functor.Comp.map id x = x
参数：x : Functor.Comp F G α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
· 使用定理 `id_map'`：∀ {f : Type u_1 → Type u_2} {α : Type u_1} [inst : Functor f] [
LawfulFunctor f] (x : f α), (fun a => a) <$> x = x
-/
protected theorem id_map : ∀ x : Comp F G α, Comp.map id x = x
  | Comp.mk x => by simp only [Comp.map, id_map, id_map']; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Functor.Comp.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：∀ {F : Type u → Type w} {G : Type v → Type u} [inst : Functor F] [inst_1 :
 Functor G] [LawfulFunctor F]   [LawfulFunctor G] {α β γ : Type v} (g' : α → β) 
(h : β → γ) (x : Functor.Comp F G α),   Functor.Comp.map (h ∘ g') x = Functor.Co
mp.map h (Functor.Comp.map g' x)
参数：g' : α → β；h : β → γ；x : Functor.Comp F G α；h ∘ g'；Functor.Comp.map g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem comp_map (g' : α → β) (h : β → γ) :
    ∀ x : Comp F G α, Comp.map (h ∘ g') x = Comp.map h (Comp.map g' x)
  | Comp.mk x => by simp [Comp.map, Comp.mk, functor_norm, Function.comp_def]
/-
**Functor.Comp.lawfulFunctor** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
形式化陈述：lawfulFunctor : LawfulFunctor (Comp F G) where map_const
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.Comp.id_map`：∀ {F : Type u → Type w} {G : Type v → Type u} [inst
 : Functor F] [inst_1 : Functor G] [LawfulFunctor F]   [LawfulFunctor G] {α : Ty
pe v} (x …
· 使用定理 `Functor.Comp.comp_map`：∀ {F : Type u → Type w} {G : Type v → Type u} [in
st : Functor F] [inst_1 : Functor G] [LawfulFunctor F]   [LawfulFunctor G] {α β 
γ : Type v}…
-/
instance lawfulFunctor : LawfulFunctor (Comp F G) where
  map_const := rfl
  id_map := Comp.id_map
  comp_map := Comp.comp_map
/-
**Functor.Comp.functor_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：functor_comp_id {F} [AF : Functor F] [LawfulFunctor F] : Comp.functor (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.ext`：Functor.ext {F} : forall {F1 : Functor F} {F2 : Functor F} 
[@LawfulFunctor F F1] [@LawfulFunctor F F2], (forall (α β) (f : α -> β) (x : F α
)…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `LawfulMonad.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : Monad m
} [self : LawfulMonad m], LawfulApplicative m
· 使用定理 `Id.instLawfulMonad`：LawfulMonad Id
-/
theorem functor_comp_id {F} [AF : Functor F] [LawfulFunctor F] :
    Comp.functor (G := Id) = AF :=
  @Functor.ext F _ AF (Comp.lawfulFunctor (G := Id)) _ fun _ _ _ _ => rfl
/-
**Functor.Comp.functor_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：functor_id_comp {F} [AF : Functor F] [LawfulFunctor F] : Comp.functor (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Functor.ext`：Functor.ext {F} : forall {F1 : Functor F} {F2 : Functor F} 
[@LawfulFunctor F F1] [@LawfulFunctor F F2], (forall (α β) (f : α -> β) (x : F α
)…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `LawfulMonad.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : Monad m
} [self : LawfulMonad m], LawfulApplicative m
· 使用定理 `Id.instLawfulMonad`：LawfulMonad Id
-/
theorem functor_id_comp {F} [AF : Functor F] [LawfulFunctor F] : Comp.functor (F := Id) = AF :=
  @Functor.ext F _ AF (Comp.lawfulFunctor (F := Id)) _ fun _ _ _ _ => rfl

end Comp

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u → Type w} {G : Type v → Type u}
variable [Applicative F] [Applicative G]

/-- The `<*>` operation for the composition of applicative functors. -/
/-
**Functor.Comp.seq** 是 Mathlib 中的一个定义，位于命名空间 `Functor.Comp`。
形式化陈述：{F : Type u → Type w} →   {G : Type v → Type u} →     [Applicative F] →   
    [Applicative G] → {α β : Type v} → Functor.Comp F G (α → β) → (Unit → Functo
r.Comp F G α) → Functor.Comp F G β
参数：α → β；Unit → Functor.Comp F G α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `<*>` operation for the composition of applicative functors.
-/
protected def seq {α β : Type v} : Comp F G (α → β) → (Unit → Comp F G α) → Comp F G β
  | Comp.mk f, g => match g () with
    | Comp.mk x => Comp.mk <| (· <*> ·) <$> f <*> x
-- `ₓ` because the type of `Seq.seq` doesn't match `has_seq.seq`
/-
**Functor.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pure (Comp F G) :=
  ⟨fun x => Comp.mk <| pure <| pure x⟩
/-
**Functor.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Seq (Comp F G) :=
  ⟨fun f x => Comp.seq f x⟩

@[simp]
/-
**Functor.Comp.run_pure** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：∀ {F : Type u → Type w} {G : Type v → Type u} [inst : Applicative F] [inst
_1 : Applicative G] {α : Type v} (x : α),   (pure x).run = pure (pure x)
参数：x : α；pure x；pure x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem run_pure {α : Type v} : ∀ x : α, (pure x : Comp F G α).run = pure (pure x)
  | _ => rfl

@[simp]
/-
**Functor.Comp.run_seq** 是 Mathlib 中的一个定理，位于命名空间 `Functor.Comp`。
形式化陈述：∀ {F : Type u → Type w} {G : Type v → Type u} [inst : Applicative F] [inst
_1 : Applicative G] {α β : Type v}   (f : Functor.Comp F G (α → β)) (x : Functor
.Comp F G α), (f <*> x).run = (fun x1 x2 => x1 <*> x2) <$> f.run <*> x.run
参数：f : Functor.Comp F G (α → β)；x : Functor.Comp F G α；f <*> x；fun x1 x2 => x1 <
*> x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem run_seq {α β : Type v} (f : Comp F G (α → β)) (x : Comp F G α) :
    (f <*> x).run = (· <*> ·) <$> f.run <*> x.run :=
  rfl
/-
**Functor.Comp.instApplicativeComp** 是 Mathlib 中的一个实例，位于命名空间 `Functor.Comp`。
形式化陈述：instApplicativeComp : Applicative (Comp F G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instApplicativeComp : Applicative (Comp F G) :=
  { map := @Comp.map F G _ _, seq := @Comp.seq F G _ _ }

end Comp

variable {F : Type u → Type v} [Functor F]

/-- If we consider `x : F α` to, in some sense, contain values of type `α`,
predicate `Liftp p x` holds iff every value contained by `x` satisfies `p`. -/
/-
**Functor.Liftp** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：Liftp {α : Type u} (p : α -> Prop) (x : F α) : Prop
参数：p : α -> Prop；x : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we consider `x : F α` to, in some sense, contain values of type `α`,
predicate `Liftp p x` holds iff every value contained by `x` satisfies `p`.
-/
def Liftp {α : Type u} (p : α → Prop) (x : F α) : Prop :=
  ∃ u : F (Subtype p), Subtype.val <$> u = x

/-- If we consider `x : F α` to, in some sense, contain values of type `α`, then
`Liftr r x y` relates `x` and `y` iff (1) `x` and `y` have the same shape and
(2) we can pair values `a` from `x` and `b` from `y` so that `r a b` holds. -/
/-
**Functor.Liftr** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：Liftr {α : Type u} (r : α -> α -> Prop) (x y : F α) : Prop
参数：r : α -> α -> Prop；x y : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we consider `x : F α` to, in some sense, contain values of type `α`, then
`Liftr r x y` relates `x` and `y` iff (1) `x` and `y` have the same shape and
(2) we can pair values `a` from `x` and `b` from `y` so that `r a b` holds.
-/
def Liftr {α : Type u} (r : α → α → Prop) (x y : F α) : Prop :=
  ∃ u : F { p : α × α // r p.fst p.snd },
    (fun t : { p : α × α // r p.fst p.snd } => t.val.fst) <$> u = x ∧
      (fun t : { p : α × α // r p.fst p.snd } => t.val.snd) <$> u = y

/-- If we consider `x : F α` to, in some sense, contain values of type `α`, then
`supp x` is the set of values of type `α` that `x` contains. -/
/-
**Functor.supp** 是 Mathlib 中的一个定义，位于命名空间 `Functor`。
形式化陈述：supp {α : Type u} (x : F α) : Set α
参数：x : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we consider `x : F α` to, in some sense, contain values of type `α`, then
`supp x` is the set of values of type `α` that `x` contains.
-/
def supp {α : Type u} (x : F α) : Set α :=
  { y : α | ∀ ⦃p⦄, Liftp p x → p y }
/-
**Functor.of_mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `Functor`。
形式化陈述：of_mem_supp {α : Type u} {x : F α} {p : α -> Prop} (h : Liftp p x) : foral
l y in supp x, p y
参数：h : Liftp p x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_mem_supp {α : Type u} {x : F α} {p : α → Prop} (h : Liftp p x) : ∀ y ∈ supp x, p y :=
  fun _ hy => hy h

/-- If `f` is a functor, if `fb : f β` and `a : α`, then `mapConstRev fb a` is the result of
  applying `f.map` to the constant function `β → α` sending everything to `a`, and then
  evaluating at `fb`. In other words it's `const a <$> fb`. -/
/-
**Functor.mapConstRev** 是 Mathlib 中的一个缩写定义，位于命名空间 `Functor`。
形式化陈述：mapConstRev {f : Type u -> Type v} [Functor f] {α β : Type u} : f β -> α -
> f α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a functor, if `fb : f β` and `a : α`, then `mapConstRev fb a` is the r
esult of
  applying `f.map` to the constant function `β → α` sending everything to `a`, a
nd then
  evaluating at `fb`. In other words it's `const a <$> fb`.
-/
abbrev mapConstRev {f : Type u → Type v} [Functor f] {α β : Type u} :
    f β → α → f α :=
  fun a b => Functor.mapConst b a
/-- If `f` is a functor, if `fb : f β` and `a : α`, then `mapConstRev fb a` is the result of
  applying `f.map` to the constant function `β → α` sending everything to `a`, and then
  evaluating at `fb`. In other words it's `const a <$> fb`. -/
infix:100 " $> " => Functor.mapConstRev

end Functor

