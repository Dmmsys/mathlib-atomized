/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Unique
public import Mathlib.Util.Notation3

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`Init.Core`).

## Tags

quotient
-/

@[expose] public section

variable {α : Sort*} {β : Sort*}

namespace Setoid

-- Pretty print `@Setoid.r _ s a b` as `s a b`.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``Setoid.r
    (some { numArgs := 2, coercee := 1, type := .coeFun })

/-- When writing a lemma about `someSetoid x y` (which uses this instance),
call it `someSetoid_apply` not `someSetoid_r`. -/
/-
**Setoid.** 是 Mathlib 中的一个实例，位于命名空间 `Setoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When writing a lemma about `someSetoid x y` (which uses this instance),
call it `someSetoid_apply` not `someSetoid_r`.
-/
instance : CoeFun (Setoid α) (fun _ ↦ α → α → Prop) where
  coe := @Setoid.r _
/-
**Setoid.ext** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a b ↔ t a b) -> 
s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {α : Sort*} : ∀ {s t : Setoid α}, (∀ a b, s a b ↔ t a b) → s = t
  | ⟨r, _⟩, ⟨p, _⟩, Eq =>
  by have : r = p := funext fun a ↦ funext fun b ↦ propext <| Eq a b
     subst this
     rfl

end Setoid

namespace Quot

variable {ra : α → α → Prop} {rb : β → β → Prop} {φ : Quot ra → Quot rb → Sort*}

@[inherit_doc Quot.mk]
local notation3:arg "⟦" a "⟧" => Quot.mk _ a

@[elab_as_elim]
/-
**Quot.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r), (∀ (
a : α), β (Quot.mk r a)) → β q
参数：q : Quot r；∀ (a : α), β (Quot.mk r a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem induction_on {α : Sort*} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r)
    (h : ∀ a, β (Quot.mk r a)) : β q :=
  ind h q
/-
**Quot.** 是 Mathlib 中的一个实例，位于命名空间 `Quot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [Inhabited α] : Inhabited (Quot r) :=
  ⟨⟦default⟧⟩
/-
**Quot.Subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：∀ {α : Sort u_1} {ra : α → α → Prop} [Subsingleton α], Subsingleton (Quot 
ra)
参数：Quot ra。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected instance Subsingleton [Subsingleton α] : Subsingleton (Quot ra) :=
  ⟨fun x ↦ Quot.induction_on x fun _ ↦ Quot.ind fun _ ↦ congr_arg _ (Subsingleton.elim _ _)⟩
/-
**Quot.** 是 Mathlib 中的一个实例，位于命名空间 `Quot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (Quot ra) := Unique.mk' _

/-- Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
/-
**Quot.hrecOn** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} →   {r : α → α → Prop} →     {motive : Quot r → Sort v} →    
   (q : Quot r) → (f : (a : α) → motive (Quot.mk r a)) → (∀ (a b : α), r a b → f
 a ≍ f b) → motive q
参数：q : Quot r；f : (a : α) → motive (Quot.mk r a)；∀ (a b : α), r a b → f a ≍ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` 
and `⟦b⟧`.
-/
protected def hrecOn₂ (qa : Quot ra) (qb : Quot rb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (ca : ∀ {b a₁ a₂}, ra a₁ a₂ → f a₁ b ≍ f a₂ b)
    (cb : ∀ {a b₁ b₂}, rb b₁ b₂ → f a b₁ ≍ f a b₂) :
    φ qa qb :=
  Quot.hrecOn (motive := fun qa ↦ φ qa qb) qa
    (fun a ↦ Quot.hrecOn qb (f a) (fun _ _ pb ↦ cb pb))
    fun a₁ a₂ pa ↦
      Quot.induction_on qb fun b ↦
        have h₁ : @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _) ≍ f a₁ b := by
          simp
        have h₂ : f a₂ b ≍ @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) := by
          simp
        (h₁.trans (ca pa)).trans h₂

/-- Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `Quot ra → Quot rb`. -/
/-
**Quot.map** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {ra : α → α → Prop} → {rb : β → β 
→ Prop} → (f : α → β) → (∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)) → Quot ra → Quot 
rb
参数：f : α → β；∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function `f : α → β` such that `ra x y` implies `rb (f x) (f y)`
to a map `Quot ra → Quot rb`.
-/
protected def map (f : α → β) (h : ∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)) : Quot ra → Quot rb :=
  Quot.lift (fun x => Quot.mk rb (f x)) fun _ _ hra ↦ Quot.sound <| h hra

/-- If `ra` is a subrelation of `ra'`, then we have a natural map `Quot ra → Quot ra'`. -/
/-
**Quot.mapRight** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u_1} → {ra ra' : α → α → Prop} → (∀ (a₁ a₂ : α), ra a₁ a₂ → ra' 
a₁ a₂) → Quot ra → Quot ra'
参数：∀ (a₁ a₂ : α), ra a₁ a₂ → ra' a₁ a₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ra` is a subrelation of `ra'`, then we have a natural map `Quot ra → Quot ra
'`.
-/
protected def mapRight {ra' : α → α → Prop} (h : ∀ a₁ a₂, ra a₁ a₂ → ra' a₁ a₂) :
    Quot ra → Quot ra' :=
  Quot.map id h

/-- Weaken the relation of a quotient. This is the same as `Quot.map id`. -/
/-
**Quot.factor** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：factor {α : Type*} (r s : α -> α -> Prop) (h : forall x y, r x y -> s x y)
 : Quot r -> Quot s
参数：r s : α -> α -> Prop；h : forall x y, r x y -> s x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weaken the relation of a quotient. This is the same as `Quot.map id`.
-/
def factor {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) : Quot r → Quot s :=
  Quot.lift (Quot.mk s) fun x y rxy ↦ Quot.sound (h x y rxy)
/-
**Quot.factor_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：factor_mk_eq {α : Type*} (r s : α -> α -> Prop) (h : forall x y, r x y -> 
s x y) : factor r s h ∘ Quot.mk _ = Quot.mk _
参数：r s : α -> α -> Prop；h : forall x y, r x y -> s x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factor_mk_eq {α : Type*} (r s : α → α → Prop) (h : ∀ x y, r x y → s x y) :
    factor r s h ∘ Quot.mk _ = Quot.mk _ :=
  rfl

variable {γ : Sort*} {r : α → α → Prop} {s : β → β → Prop}
/-
**Quot.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：lift_mk (f : α -> γ) (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) (a : α) : 
Quot.lift f h (Quot.mk r a) = f a
参数：f : α -> γ；h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a :=
  rfl
/-
**Quot.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：liftOn_mk (a : α) (f : α -> γ) (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) 
: Quot.liftOn (Quot.mk r a) f h = f a
参数：a : α；f : α -> γ；h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a :=
  rfl
/-
**Quot.surjective_lift** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：∀ {α : Sort u_1} {γ : Sort u_4} {r : α → α → Prop} {f : α → γ} (h : ∀ (a₁ 
a₂ : α), r a₁ a₂ → f a₁ = f a₂),   Function.Surjective (Quot.lift f h) ↔ Functio
n.Surjective f
参数：h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂；Quot.lift f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
@[simp] theorem surjective_lift {f : α → γ} (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Function.Surjective (lift f h) ↔ Function.Surjective f :=
  ⟨fun hf => hf.comp Quot.exists_rep, fun hf y => let ⟨x, hx⟩ := hf y; ⟨Quot.mk _ x, hx⟩⟩

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β`. -/
/-
**Quot.lift** 是 Mathlib 中的一个quot，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) → (∀ (a b :
 α), r a b → f a = f b) → Quot r → β
参数：f : α → β；∀ (a b : α), r a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Descends a function `f : α → β → γ` to quotients of `α` and `β`.
-/
protected def lift₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a ↦ Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha ↦ funext fun q ↦ Quot.induction_on q fun b ↦ hs a₁ a₂ b ha) q₁ q₂

@[simp]
/-
**Quot.lift** 是 Mathlib 中的一个quot，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) → (∀ (a b :
 α), r a b → f a = f b) → Quot r → β
参数：f : α → β；∀ (a b : α), r a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    (a : α) (b : β) : Quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it. -/
/-
**Quot.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {β : Sort v} → {r : α → α → Prop} → Quot r → (f : α → β) → 
(∀ (a b : α), r a b → f a = f b) → β
参数：f : α → β；∀ (a b : α), r a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Descends a function `f : α → β → γ` to quotients of `α` and `β` and applies it.
-/
protected def liftOn₂ (p : Quot r) (q : Quot s) (f : α → β → γ)
    (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q

@[simp]
/-
**Quot.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {β : Sort v} → {r : α → α → Prop} → Quot r → (f : α → β) → 
(∀ (a b : α), r a b → f a = f b) → β
参数：f : α → β；∀ (a b : α), r a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_mk (a : α) (b : β) (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b) :
    Quot.liftOn₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl

variable {t : γ → γ → Prop}

/-- Descends a function `f : α → β → γ` to quotients of `α` and `β` with values in a quotient of
`γ`. -/
/-
**Quot.map** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {ra : α → α → Prop} → {rb : β → β 
→ Prop} → (f : α → β) → (∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)) → Quot ra → Quot 
rb
参数：f : α → β；∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Descends a function `f : α → β → γ` to quotients of `α` and `β` with values in a
 quotient of
`γ`.
-/
protected def map₂ (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b ↦ Quot.mk t <| f a b) (fun a b₁ b₂ hb ↦ Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha ↦ Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]
/-
**Quot.map** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {ra : α → α → Prop} → {rb : β → β 
→ Prop} → (f : α → β) → (∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)) → Quot ra → Quot 
rb
参数：f : α → β；∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_mk (f : α → β → γ) (hr : ∀ a b₁ b₂, s b₁ b₂ → t (f a b₁) (f a b₂))
    (hs : ∀ a₁ a₂ b, r a₁ a₂ → t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    Quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl

/-- A binary version of `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
/-
**Quot.recOnSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} →   {r : α → α → Prop} →     {motive : Quot r → Sort v} →    
   [h : ∀ (a : α), Subsingleton (motive (Quot.mk r a))] → (q : Quot r) → ((a : α
) → motive (Quot.mk r a)) → motive q
参数：a : α；motive (Quot.mk r a)；q : Quot r；(a : α) → motive (Quot.mk r a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary version of `Quot.recOnSubsingleton`.
-/
protected def recOnSubsingleton₂ {φ : Quot r → Quot s → Sort*}
    [h : ∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r)
    (q₂ : Quot s) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quot.recOnSubsingleton _ r (fun q ↦ φ q q₂)
    (fun a ↦ Quot.ind (β := fun b ↦ Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a ↦ Quot.recOnSubsingleton q₂ fun b ↦ f a b

@[elab_as_elim]
/-
**Quot.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r), (∀ (
a : α), β (Quot.mk r a)) → β q
参数：q : Quot r；∀ (a : α), β (Quot.mk r a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem induction_on₂ {δ : Quot r → Quot s → Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : ∀ a b, δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (β := fun a ↦ δ a q₂) (fun a₁ ↦ Quot.ind (fun a₂ ↦ h a₁ a₂) q₂) q₁

@[elab_as_elim]
/-
**Quot.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Quot`。
形式化陈述：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Prop} (q : Quot r), (∀ (
a : α), β (Quot.mk r a)) → β q
参数：q : Quot r；∀ (a : α), β (Quot.mk r a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem induction_on₃ {δ : Quot r → Quot s → Quot t → Prop} (q₁ : Quot r)
    (q₂ : Quot s) (q₃ : Quot t) (h : ∀ a b c, δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) :
    δ q₁ q₂ q₃ :=
  Quot.ind (β := fun a ↦ δ a q₂ q₃) (fun a₁ ↦ Quot.ind (β := fun b ↦ δ _ b q₃)
    (fun a₂ ↦ Quot.ind (fun a₃ ↦ h a₁ a₂ a₃) q₃) q₂) q₁
/-
**Quot.lift.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Quot.lift`。
形式化陈述：{α : Sort u_1} →   (r : α → α → Prop) →     (f : α → Prop) → (h : ∀ (a b :
 α), r a b → f a = f b) → [hf : DecidablePred f] → DecidablePred (Quot.lift f h)
参数：r : α → α → Prop；f : α → Prop；h : ∀ (a b : α), r a b → f a = f b；Quot.lift f 
h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lift.decidablePred (r : α → α → Prop) (f : α → Prop) (h : ∀ a b, r a b → f a = f b)
    [hf : DecidablePred f] :
    DecidablePred (Quot.lift f h) :=
  fun q ↦ Quot.recOnSubsingleton (motive := fun _ ↦ Decidable _) q hf

/-- Note that this provides `DecidableRel (Quot.Lift₂ f ha hb)` when `α = β`. -/
/-
**Quot.lift** 是 Mathlib 中的一个quot，位于命名空间 `Quot`。
形式化陈述：{α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) → (∀ (a b :
 α), r a b → f a = f b) → Quot r → β
参数：f : α → β；∀ (a b : α), r a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `DecidableRel (Quot.Lift₂ f ha hb)` when `α = β`.
-/
instance lift₂.decidablePred (r : α → α → Prop) (s : β → β → Prop) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    [hf : ∀ a, DecidablePred (f a)] (q₁ : Quot r) :
    DecidablePred (Quot.lift₂ f ha hb q₁) :=
  fun q₂ ↦ Quot.recOnSubsingleton₂ q₁ q₂ hf
/-
**Quot.** 是 Mathlib 中的一个实例，位于命名空间 `Quot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) (q : Quot r) (f : α → Prop) (h : ∀ a b, r a b → f a = f b)
    [DecidablePred f] :
    Decidable (Quot.liftOn q f h) :=
  Quot.lift.decidablePred _ _ _ _
/-
**Quot.** 是 Mathlib 中的一个实例，位于命名空间 `Quot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) (s : β → β → Prop) (q₁ : Quot r) (q₂ : Quot s) (f : α → β → Prop)
    (ha : ∀ a b₁ b₂, s b₁ b₂ → f a b₁ = f a b₂) (hb : ∀ a₁ a₂ b, r a₁ a₂ → f a₁ b = f a₂ b)
    [∀ a, DecidablePred (f a)] :
    Decidable (Quot.liftOn₂ q₁ q₂ f ha hb) :=
  Quot.lift₂.decidablePred _ _ _ _ _ _ _

end Quot

namespace Quotient

variable {sa : Setoid α} {sb : Setoid β}
variable {φ : Quotient sa → Quotient sb → Sort*}

-- TODO: in mathlib3 this notation took the Setoid as an instance-implicit argument,
-- now it's explicit but left as a metavariable.
-- We have not yet decided which one works best, since the setoid instance can't always be
-- reliably found but it can't always be inferred from the expected type either.
-- See also: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
@[inherit_doc Quotient.mk]
notation3:arg "⟦" a "⟧" => Quotient.mk _ a

/-
**Quotient.instInhabitedQuotient** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
形式化陈述：instInhabitedQuotient (s : Setoid α) [Inhabited α] : Inhabited (Quotient s
)
参数：s : Setoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabitedQuotient (s : Setoid α) [Inhabited α] : Inhabited (Quotient s) :=
  ⟨⟦default⟧⟩
/-
**Quotient.instSubsingletonQuotient** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
形式化陈述：instSubsingletonQuotient (s : Setoid α) [Subsingleton α] : Subsingleton (Q
uotient s)
参数：s : Setoid α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.Subsingleton`：∀ {α : Sort u_1} {ra : α → α → Prop} [Subsingleton α]
, Subsingleton (Quot ra)
-/
instance instSubsingletonQuotient (s : Setoid α) [Subsingleton α] : Subsingleton (Quotient s) :=
  Quot.Subsingleton
/-
**Quotient.instUniqueQuotient** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
形式化陈述：instUniqueQuotient (s : Setoid α) [Unique α] : Unique (Quotient s)
参数：s : Setoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniqueQuotient (s : Setoid α) [Unique α] : Unique (Quotient s) := Unique.mk' _
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Setoid α] : IsEquiv α (· ≈ ·) where
  refl := Setoid.refl
  symm _ _ := Setoid.symm
  trans _ _ _ := Setoid.trans

/-- Induction on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
/-
**Quotient.hrecOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} →   {s : Setoid α} →     {motive : Quotient s → Sort v} →    
   (q : Quotient s) → (f : (a : α) → motive ⟦a⟧) → (∀ (a b : α), a ≈ b → f a ≍ f
 b) → motive q
参数：q : Quotient s；f : (a : α) → motive ⟦a⟧；∀ (a b : α), a ≈ b → f a ≍ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` 
and `⟦b⟧`.
-/
protected def hrecOn₂ (qa : Quotient sa) (qb : Quotient sb) (f : ∀ a b, φ ⟦a⟧ ⟦b⟧)
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ ≍ f a₂ b₂) : φ qa qb :=
  Quot.hrecOn₂ qa qb f (fun p ↦ c _ _ _ _ p (Setoid.refl _)) fun p ↦ c _ _ _ _ (Setoid.refl _) p

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on quotients. -/
/-
**Quotient.map** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {sa : Setoid α} → {sb : Setoid β} 
→ (f : α → β) → (∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) → Quotient sa → Quotient sb
参数：f : α → β；∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on 
quotients.
-/
protected def map (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) : Quotient sa → Quotient sb :=
  Quot.map f h

@[simp]
/-
**Quotient.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：map_mk (f : α -> β) (h) (x : α) : Quotient.map f h (⟦x⟧ : Quotient sa) = (
⟦f x⟧ : Quotient sb)
参数：f : α -> β；h；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (f : α → β) (h) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  rfl

variable {γ : Sort*} {sc : Setoid γ}

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : Quotient sa → Quotient sb → Quotient sc`.
Useful to define binary operations on quotients. -/
/-
**Quotient.map** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {sa : Setoid α} → {sb : Setoid β} 
→ (f : α → β) → (∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) → Quotient sa → Quotient sb
参数：f : α → β；∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function `f : α → β → γ` that sends equivalent elements to equivalent elem
ents
to a function `f : Quotient sa → Quotient sb → Quotient sc`.
Useful to define binary operations on quotients.
-/
protected def map₂ (f : α → β → γ)
    (h : ∀ ⦃a₁ a₂⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂⦄, b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y ↦ ⟦f x y⟧) fun _ _ _ _ h₁ h₂ ↦ Quot.sound <| h h₁ h₂

@[simp]
/-
**Quotient.map** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {sa : Setoid α} → {sb : Setoid β} 
→ (f : α → β) → (∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) → Quotient sa → Quotient sb
参数：f : α → β；∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_mk (f : α → β → γ) (h) (x : α) (y : β) :
    Quotient.map₂ f h (⟦x⟧ : Quotient sa) (⟦y⟧ : Quotient sb) = (⟦f x y⟧ : Quotient sc) :=
  rfl
/-
**Quotient.lift.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Quotient.lift`。
形式化陈述：{α : Sort u_1} →   {sa : Setoid α} →     (f : α → Prop) → (h : ∀ (a b : α)
, a ≈ b → f a = f b) → [DecidablePred f] → DecidablePred (Quotient.lift f h)
参数：f : α → Prop；h : ∀ (a b : α), a ≈ b → f a = f b；Quotient.lift f h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lift.decidablePred (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    DecidablePred (Quotient.lift f h) :=
  Quot.lift.decidablePred _ _ _

/-- Note that this provides `DecidableRel (Quotient.lift₂ f h)` when `α = β`. -/
/-
**Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {β : Sort v} → {s : Setoid α} → (f : α → β) → (∀ (a b : α),
 a ≈ b → f a = f b) → Quotient s → β
参数：f : α → β；∀ (a b : α), a ≈ b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `DecidableRel (Quotient.lift₂ f h)` when `α = β`.
-/
instance lift₂.decidablePred (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    [hf : ∀ a, DecidablePred (f a)]
    (q₁ : Quotient sa) : DecidablePred (Quotient.lift₂ f h q₁) :=
  fun q₂ ↦ Quotient.recOnSubsingleton₂ q₁ q₂ hf
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (q : Quotient sa) (f : α → Prop) (h : ∀ a b, a ≈ b → f a = f b) [DecidablePred f] :
    Decidable (Quotient.liftOn q f h) :=
  Quotient.lift.decidablePred _ _ _
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (q₁ : Quotient sa) (q₂ : Quotient sb) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) [∀ a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂ q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end Quotient

/-
**Quot.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r x = Quot.mk
 r y ↔ Relation.EqvGen r x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eqvGen_exact`：Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : E
qvGen r a b
· 使用定理 `Quot.eqvGen_sound`：Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = 
Quot.mk r b
-/
theorem Quot.eq {α : Type*} {r : α → α → Prop} {x y : α} :
    Quot.mk r x = Quot.mk r y ↔ Relation.EqvGen r x y :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

-- This should not be a `@[simp]` lemma,
-- as this prevents us from using `simp` reliably in the quotient,
-- because this might bump us back out from equality to the underlying relation.
/-
**Quotient.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ r x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ r x y :=
  ⟨Quotient.exact, Quotient.sound⟩
/-
**Quotient.eq_iff_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ x
 ≈ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ x ≈ y :=
  Quotient.eq
/-
**Quotient.forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotient s -> Prop} : (for
all a, p a) ↔ forall a : α, p ⟦a⟧
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
theorem Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotient s → Prop} :
    (∀ a, p a) ↔ ∀ a : α, p ⟦a⟧ :=
  ⟨fun h _ ↦ h _, fun h a ↦ a.ind h⟩
/-
**Quotient.exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.exists {α : Sort*} {s : Setoid α} {p : Quotient s -> Prop} : (exi
sts a, p a) ↔ exists a : α, p ⟦a⟧
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
theorem Quotient.exists {α : Sort*} {s : Setoid α} {p : Quotient s → Prop} :
    (∃ a, p a) ↔ ∃ a : α, p ⟦a⟧ :=
  ⟨fun ⟨q, hq⟩ ↦ q.ind (motive := (p · → _)) .intro hq, fun ⟨a, ha⟩ ↦ ⟨⟦a⟧, ha⟩⟩

@[simp]
/-
**Quotient.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b ->
 f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = f x
参数：f : α -> β；h : forall a b : α, a ≈ b -> f a = f b；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.lift_mk {s : Setoid α} (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk s x) = f x :=
  rfl

@[simp]
/-
**Quotient.lift_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.lift_comp_mk {_ : Setoid α} (f : α -> β) (h : forall a b : α, a ≈
 b -> f a = f b) : Quotient.lift f h ∘ Quotient.mk _ = f
参数：f : α -> β；h : forall a b : α, a ≈ b -> f a = f b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.lift_comp_mk {_ : Setoid α} (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) :
    Quotient.lift f h ∘ Quotient.mk _ = f :=
  rfl

@[simp]
/-
**Quotient.lift_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.lift_surjective_iff {α β : Sort*} {s : Setoid α} (f : α -> β) (h 
: forall (a b : α), a ≈ b -> f a = f b) : Function.Surjective (Quotient.lift f h
 : Quotient s -> β) ↔ Function.Surjective f
参数：f : α -> β；h : forall (a b : α), a ≈ b -> f a = f b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.surjective_lift`：∀ {α : Sort u_1} {γ : Sort u_4} {r : α → α → Prop}
 {f : α → γ} (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂),   Function.Surjective (
Quot.lift …
-/
theorem Quotient.lift_surjective_iff {α β : Sort*} {s : Setoid α} (f : α → β)
    (h : ∀ (a b : α), a ≈ b → f a = f b) :
    Function.Surjective (Quotient.lift f h : Quotient s → β) ↔ Function.Surjective f :=
  Quot.surjective_lift h
/-
**Quotient.lift_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.lift_surjective {α β : Sort*} {s : Setoid α} (f : α -> β) (h : fo
rall (a b : α), a ≈ b -> f a = f b) (hf : Function.Surjective f) : Function.Surj
ective (Quotient.lift f h : Quotient s -> β)
参数：f : α -> β；h : forall (a b : α), a ≈ b -> f a = f b；hf : Function.Surjective 
f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quot.surjective_lift`：∀ {α : Sort u_1} {γ : Sort u_4} {r : α → α → Prop}
 {f : α → γ} (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂),   Function.Surjective (
Quot.lift …
-/
theorem Quotient.lift_surjective {α β : Sort*} {s : Setoid α} (f : α → β)
    (h : ∀ (a b : α), a ≈ b → f a = f b) (hf : Function.Surjective f) :
    Function.Surjective (Quotient.lift f h : Quotient s → β) :=
  (Quot.surjective_lift h).mpr hf

@[simp]
/-
**Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {β : Sort v} → {s : Setoid α} → (f : α → β) → (∀ (a b : α),
 a ≈ b → f a = f b) → Quotient s → β
参数：f : α → β；∀ (a b : α), a ≈ b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.lift₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} {_ : Setoid α} {_ : Setoid β}
    (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) :
    Quotient.lift₂ f h (Quotient.mk _ a) (Quotient.mk _ b) = f a b :=
  rfl
/-
**Quotient.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.liftOn_mk {s : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b 
-> f a = f b) (x : α) : Quotient.liftOn (Quotient.mk s x) f h = f x
参数：f : α -> β；h : forall a b : α, a ≈ b -> f a = f b；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.liftOn_mk {s : Setoid α} (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
    Quotient.liftOn (Quotient.mk s x) f h = f x :=
  rfl

@[simp]
/-
**Quotient.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {β : Sort v} → {s : Setoid α} → Quotient s → (f : α → β) → 
(∀ (a b : α), a ≈ b → f a = f b) → β
参数：f : α → β；∀ (a b : α), a ≈ b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.liftOn₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} {_ : Setoid α} {_ : Setoid β}
    (f : α → β → γ)
    (h : ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    (x : α) (y : β) :
    Quotient.liftOn₂ (Quotient.mk _ x) (Quotient.mk _ y) f h = f x y :=
  rfl

/-- `Quot.mk r` is a surjective function. -/
/-
**Quot.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.mk_surjective {r : α -> α -> Prop} : Function.Surjective (Quot.mk r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q

--- 原说明 ---
`Quot.mk r` is a surjective function.
-/
theorem Quot.mk_surjective {r : α → α → Prop} : Function.Surjective (Quot.mk r) :=
  Quot.exists_rep

/-- `Quotient.mk` is a surjective function. -/
/-
**Quotient.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.mk_surjective {s : Setoid α} : Function.Surjective (Quotient.mk s
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)

--- 原说明 ---
`Quotient.mk` is a surjective function.
-/
theorem Quotient.mk_surjective {s : Setoid α} :
    Function.Surjective (Quotient.mk s) :=
  Quot.mk_surjective

/-- `Quotient.mk'` is a surjective function. -/
/-
**Quotient.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} [s : Setoid α], Function.Surjective Quotient.mk'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)

--- 原说明 ---
`Quotient.mk'` is a surjective function.
-/
theorem Quotient.mk'_surjective [s : Setoid α] :
    Function.Surjective (Quotient.mk' : α → Quotient s) :=
  Quot.mk_surjective
/-
**Quot.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.map_surjective {ra : α -> α -> Prop} {rb : β -> β -> Prop} {f : α -> 
β} .Surjective
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quot.surjective_lift`：∀ {α : Sort u_1} {γ : Sort u_4} {r : α → α → Prop}
 {f : α → γ} (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂),   Function.Surjective (
Quot.lift …
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem Quot.map_surjective {ra : α → α → Prop} {rb : β → β → Prop} {f : α → β}
    (h : ∀ ⦃a b : α⦄, ra a b → rb (f a) (f b)) (hf : f.Surjective) : Quot.map f h |>.Surjective :=
  surjective_lift _ |>.mpr <| .comp Quot.mk_surjective hf
/-
**Quotient.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.map_surjective {sa : Setoid α} {sb : Setoid β} {f : α -> β} .Surj
ective
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.lift_surjective`：Quotient.lift_surjective {α β : Sort*} {s : Se
toid α} (f : α -> β) (h : forall (a b : α), a ≈ b -> f a = f b) (hf : Function.S
urjective f) :…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem Quotient.map_surjective {sa : Setoid α} {sb : Setoid β} {f : α → β}
    (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) (hf : f.Surjective) : Quotient.map f h |>.Surjective :=
  lift_surjective _ _ <| .comp Quot.mk_surjective hf

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
/-
**Quot.out** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quot.out {r : α -> α -> Prop} (q : Quot r) : α
参数：q : Quot r。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q

--- 原说明 ---
Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable.
-/
noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
/-
**Quot.unquot** 是 Mathlib 中的一个unsafe-def，位于命名空间 `Quot`。
形式化陈述：{α : Sort u_1} → {r : α → α → Prop} → Quot r → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unwrap the VM representation of a quotient to obtain an element of the equivalen
ce class.
  Computable but unsound.
-/
unsafe def Quot.unquot {r : α → α → Prop} : Quot r → α :=
  cast lcProof

@[simp]
/-
**Quot.out_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q.out = q
参数：q : Quot r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem Quot.out_eq {r : α → α → Prop} (q : Quot r) : Quot.mk r q.out = q :=
  Classical.choose_spec (Quot.exists_rep q)

/-- Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable. -/
/-
**Quotient.out** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quotient.out {s : Setoid α} : Quotient s -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choose an element of the equivalence class using the axiom of choice.
  Sound but noncomputable.
-/
noncomputable def Quotient.out {s : Setoid α} : Quotient s → α :=
  Quot.out

@[simp]
/-
**Quotient.out_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.out⟧ = q
参数：q : Quotient s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
theorem Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.out⟧ = q :=
  Quot.out_eq q
/-
**Quotient.mk_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quotient s).out a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quotient s).out a :=
  Quotient.exact (Quotient.out_eq _)
/-
**Quotient.mk_eq_iff_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y : Quotient s} : ⟦x⟧ = y ↔
 x ≈ Quotient.out y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y : Quotient s} :
    ⟦x⟧ = y ↔ x ≈ Quotient.out y := by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq y]
/-
**Quotient.eq_mk_iff_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.eq_mk_iff_out {s : Setoid α} {x : Quotient s} {y : α} : x = ⟦y⟧ ↔
 Quotient.out x ≈ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem Quotient.eq_mk_iff_out {s : Setoid α} {x : Quotient s} {y : α} :
    x = ⟦y⟧ ↔ Quotient.out x ≈ y := by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq x]

@[simp]
/-
**Quotient.out_equiv_out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.out_equiv_out {s : Setoid α} {x y : Quotient s} : x.out ≈ y.out ↔
 x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.eq_mk_iff_out`：Quotient.eq_mk_iff_out {s : Setoid α} {x : Quoti
ent s} {y : α} : x = ⟦y⟧ ↔ Quotient.out x ≈ y
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Quotient.out_equiv_out {s : Setoid α} {x y : Quotient s} : x.out ≈ y.out ↔ x = y := by
  rw [← Quotient.eq_mk_iff_out, Quotient.out_eq]
/-
**Quotient.out_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.out_injective {s : Setoid α} : Function.Injective (@Quotient.out 
α s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.out_equiv_out`：Quotient.out_equiv_out {s : Setoid α} {x y : Quo
tient s} : x.out ≈ y.out ↔ x = y
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
theorem Quotient.out_injective {s : Setoid α} : Function.Injective (@Quotient.out α s) :=
  fun _ _ h ↦ Quotient.out_equiv_out.1 <| h ▸ Setoid.refl _

@[simp]
/-
**Quotient.out_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.out_inj {s : Setoid α} {x y : Quotient s} : x.out = y.out ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_injective`：Quotient.out_injective {s : Setoid α} : Function
.Injective (@Quotient.out α s)
-/
theorem Quotient.out_inj {s : Setoid α} {x y : Quotient s} : x.out = y.out ↔ x = y :=
  ⟨fun h ↦ Quotient.out_injective h, fun h ↦ h ▸ rfl⟩

section Pi

/-
**piSetoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：piSetoid {ι : Sort*} {α : ι -> Sort*} [forall i, Setoid (α i)] : Setoid (f
orall i, α i) where r a b
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance piSetoid {ι : Sort*} {α : ι → Sort*} [∀ i, Setoid (α i)] : Setoid (∀ i, α i) where
  r a b := ∀ i, a i ≈ b i
  iseqv := ⟨fun _ _ ↦ Setoid.refl _,
            fun h _ ↦ Setoid.symm (h _),
            fun h₁ h₂ _ ↦ Setoid.trans (h₁ _) (h₂ _)⟩

/-- Given a class of functions `q : @Quotient (∀ i, α i) _`, returns the class of `i`-th projection
`Quotient (S i)`. -/
/-
**Quotient.eval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quotient.eval {ι : Type*} {α : ι -> Sort*} {S : forall i, Setoid (α i)} (q
 : @Quotient (forall i, α i) (by infer_instance)) (i : ι) : Quotient (S i)
参数：α i；q : @Quotient (forall i, α i) (by infer_instance)；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a class of functions `q : @Quotient (∀ i, α i) _`, returns the class of `i
`-th projection
`Quotient (S i)`.
-/
def Quotient.eval {ι : Type*} {α : ι → Sort*} {S : ∀ i, Setoid (α i)}
    (q : @Quotient (∀ i, α i) (by infer_instance)) (i : ι) : Quotient (S i) :=
  q.map (· i) fun _ _ h ↦ by exact h i

@[simp]
/-
**Quotient.eval_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.eval_mk {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)}
 (f : forall i, α i) : Quotient.eval (S
参数：α i；f : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.eval_mk {ι : Type*} {α : ι → Type*} {S : ∀ i, Setoid (α i)} (f : ∀ i, α i) :
    Quotient.eval (S := S) ⟦f⟧ = fun i ↦ ⟦f i⟧ :=
  rfl

/-- Given a function `f : Π i, Quotient (S i)`, returns the class of functions `Π i, α i` sending
each `i` to an element of the class `f i`. -/
/-
**Quotient.choice** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quotient.choice {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)} 
(f : forall i, Quotient (S i)) : @Quotient (forall i, α i) (by infer_instance)
参数：α i；f : forall i, Quotient (S i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : Π i, Quotient (S i)`, returns the class of functions `Π i,
 α i` sending
each `i` to an element of the class `f i`.
-/
noncomputable def Quotient.choice {ι : Type*} {α : ι → Type*} {S : ∀ i, Setoid (α i)}
    (f : ∀ i, Quotient (S i)) :
    @Quotient (∀ i, α i) (by infer_instance) :=
  ⟦fun i ↦ (f i).out⟧

@[simp]
/-
**Quotient.choice_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.choice_eq {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i
)} (f : forall i, α i) : (Quotient.choice (S
参数：α i；f : forall i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Quotient.mk_out`：Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quoti
ent s).out a
-/
theorem Quotient.choice_eq {ι : Type*} {α : ι → Type*} {S : ∀ i, Setoid (α i)} (f : ∀ i, α i) :
    (Quotient.choice (S := S) fun i ↦ ⟦f i⟧) = ⟦f⟧ :=
  Quotient.sound fun _ ↦ Quotient.mk_out _

@[elab_as_elim]
/-
**Quotient.induction_on_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.induction_on_pi {ι : Type*} {α : ι -> Sort*} {s : forall i, Setoi
d (α i)} {p : (forall i, Quotient (s i)) -> Prop} (f : forall i, Quotient (s i))
 (h : forall a : forall i, α i, p fun i => ⟦a i⟧) : p f
参数：α i；forall i, Quotient (s i)；f : forall i, Quotient (s i)；h : forall a : fora
ll i, α i, p fun i => ⟦a i⟧。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem Quotient.induction_on_pi {ι : Type*} {α : ι → Sort*} {s : ∀ i, Setoid (α i)}
    {p : (∀ i, Quotient (s i)) → Prop} (f : ∀ i, Quotient (s i))
    (h : ∀ a : ∀ i, α i, p fun i ↦ ⟦a i⟧) : p f := by
  rw [← (funext fun i ↦ Quotient.out_eq (f i) : (fun i ↦ ⟦(f i).out⟧) = f)]
  apply h

end Pi

/-
**nonempty_quotient_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α
参数：s : Setoid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ ↦ Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ ↦ ⟨⟦a⟧⟩⟩

/-! ### Truncation -/


/-
**true_equivalence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：true_equivalence : @Equivalence α fun _ _ => True
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
### Truncation
-/
theorem true_equivalence : @Equivalence α fun _ _ ↦ True :=
  ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩

/-- Always-true relation as a `Setoid`.

Note that in later files the preferred spelling is `⊤ : Setoid α`. -/
@[instance_reducible]
/-
**trueSetoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：trueSetoid : Setoid α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `true_equivalence`：true_equivalence : @Equivalence α fun _ _ => True

--- 原说明 ---
Always-true relation as a `Setoid`.

Note that in later files the preferred spelling is `⊤ : Setoid α`.
-/
def trueSetoid : Setoid α :=
  ⟨_, true_equivalence⟩

/-- `Trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `Nonempty α`, but unlike `Nonempty α`, `Trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability. -/
/-
**Trunc.** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Trunc α` is the quotient of `α` by the always-true relation. This
  is related to the propositional truncation in HoTT, and is similar
  in effect to `Nonempty α`, but unlike `Nonempty α`, `Trunc α` is data,
  so the VM representation is the same as `α`, and so this can be used to
  maintain computability.
-/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quotient α trueSetoid

namespace Trunc

/-- Constructor for `Trunc α` -/
/-
**Trunc.mk** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：mk (a : α) : Trunc α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Trunc α`
-/
def mk (a : α) : Trunc α :=
  Quot.mk _ a
/-
**Trunc.** 是 Mathlib 中的一个实例，位于命名空间 `Trunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨mk default⟩

/-- Any constant function lifts to a function out of the truncation -/
/-
**Trunc.lift** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：lift (f : α -> β) (c : forall a b : α, f a = f b) : Trunc α -> β
参数：f : α -> β；c : forall a b : α, f a = f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any constant function lifts to a function out of the truncation
-/
def lift (f : α → β) (c : ∀ a b : α, f a = f b) : Trunc α → β :=
  Quot.lift f fun a b _ ↦ c a b
/-
**Trunc.ind** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：ind {β : Trunc α -> Prop} : (forall a : α, β (mk a)) -> forall q : Trunc α
, β q
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ind {β : Trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : Trunc α, β q :=
  Quot.ind
/-
**Trunc.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (c : ∀ (a b : α), f a = f b) (
a : α), Trunc.lift f c (Trunc.mk a) = f a
参数：f : α → β；c : ∀ (a b : α), f a = f b；a : α；Trunc.mk a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem lift_mk (f : α → β) (c) (a : α) : lift f c (mk a) = f a :=
  rfl

/-- Lift a constant function on `q : Trunc α`. -/
/-
**Trunc.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：{α : Sort u_1} → {β : Sort u_2} → Trunc α → (f : α → β) → (∀ (a b : α), f 
a = f b) → β
参数：f : α → β；∀ (a b : α), f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a constant function on `q : Trunc α`.
-/
protected def liftOn (q : Trunc α) (f : α → β) (c : ∀ a b : α, f a = f b) : β :=
  lift f c q

@[elab_as_elim]
/-
**Trunc.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α), (∀ (a : α), β (Trunc.
mk a)) → β q
参数：q : Trunc α；∀ (a : α), β (Trunc.mk a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.ind`：ind {β : Trunc α -> Prop} : (forall a : α, β (mk a)) -> foral
l q : Trunc α, β q
-/
protected theorem induction_on {β : Trunc α → Prop} (q : Trunc α) (h : ∀ a, β (mk a)) : β q :=
  ind h q
/-
**Trunc.exists_rep** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：exists_rep (q : Trunc α) : exists a : α, mk a = q
参数：q : Trunc α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem exists_rep (q : Trunc α) : ∃ a : α, mk a = q :=
  Quot.exists_rep q

@[elab_as_elim]
/-
**Trunc.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：∀ {α : Sort u_1} {β : Trunc α → Prop} (q : Trunc α), (∀ (a : α), β (Trunc.
mk a)) → β q
参数：q : Trunc α；∀ (a : α), β (Trunc.mk a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.ind`：ind {β : Trunc α -> Prop} : (forall a : α, β (mk a)) -> foral
l q : Trunc α, β q
-/
protected theorem induction_on₂ {C : Trunc α → Trunc β → Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
  Trunc.induction_on q₁ fun a₁ ↦ Trunc.induction_on q₂ (h a₁)
/-
**Trunc.eq** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：∀ {α : Sort u_1} (a b : Trunc α), a = b
参数：a b : Trunc α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {C : Trunc α → Trun
c β → Prop} (q₁ : Trunc α) (q₂ : Trunc β),   (∀ (a : α) (b : β), C (Trunc.mk a) 
(Trunc.mk…
· 使用定理 `trivial`：True
-/
protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun _ _ ↦ Quot.sound trivial
/-
**Trunc.instSubsingletonTrunc** 是 Mathlib 中的一个实例，位于命名空间 `Trunc`。
形式化陈述：instSubsingletonTrunc : Subsingleton (Trunc α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.eq`：∀ {α : Sort u_1} (a b : Trunc α), a = b
-/
instance instSubsingletonTrunc : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

/-- The `bind` operator for the `Trunc` monad. -/
/-
**Trunc.bind** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：bind (q : Trunc α) (f : α -> Trunc β) : Trunc β
参数：q : Trunc α；f : α -> Trunc β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `bind` operator for the `Trunc` monad.
-/
def bind (q : Trunc α) (f : α → Trunc β) : Trunc β :=
  Trunc.liftOn q f fun _ _ ↦ Trunc.eq _ _

/-- A function `f : α → β` defines a function `map f : Trunc α → Trunc β`. -/
/-
**Trunc.map** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：map (f : α -> β) (q : Trunc α) : Trunc β
参数：f : α -> β；q : Trunc α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` defines a function `map f : Trunc α → Trunc β`.
-/
def map (f : α → β) (q : Trunc α) : Trunc β :=
  bind q (Trunc.mk ∘ f)
/-
**Trunc.** 是 Mathlib 中的一个实例，位于命名空间 `Trunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad Trunc where
  pure := @Trunc.mk
  bind := @Trunc.bind
/-
**Trunc.** 是 Mathlib 中的一个实例，位于命名空间 `Trunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad Trunc where
  id_map _ := Trunc.eq _ _
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := Trunc.eq _ _
  map_const := rfl
  seqLeft_eq _ _ := Trunc.eq _ _
  seqRight_eq _ _ := Trunc.eq _ _
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl

variable {C : Trunc α → Sort*}

/-- Recursion/induction principle for `Trunc`. -/
@[elab_as_elim]
/-
**Trunc.rec** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：{α : Sort u_1} →   {C : Trunc α → Sort u_3} → (f : (a : α) → C (Trunc.mk a
)) → (∀ (a b : α), ⋯ ▸ f a = f b) → (q : Trunc α) → C q
参数：f : (a : α) → C (Trunc.mk a)；∀ (a b : α), ⋯ ▸ f a = f b；q : Trunc α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion/induction principle for `Trunc`.
-/
protected def rec (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
    (q : Trunc α) : C q :=
  Quot.rec f (fun a b _ ↦ h a b) q

/-- A version of `Trunc.rec` taking `q : Trunc α` as the first argument. -/
@[elab_as_elim]
/-
**Trunc.recOn** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：{α : Sort u_1} →   {C : Trunc α → Sort u_3} → (q : Trunc α) → (f : (a : α)
 → C (Trunc.mk a)) → (∀ (a b : α), ⋯ ▸ f a = f b) → C q
参数：q : Trunc α；f : (a : α) → C (Trunc.mk a)；∀ (a b : α), ⋯ ▸ f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Trunc.rec` taking `q : Trunc α` as the first argument.
-/
protected def recOn (q : Trunc α) (f : ∀ a, C (mk a))
    (h : ∀ a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
  Trunc.rec f h q

/-- A version of `Trunc.recOn` assuming the codomain is a `Subsingleton`. -/
@[elab_as_elim]
/-
**Trunc.recOnSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：{α : Sort u_1} →   {C : Trunc α → Sort u_3} →     [∀ (a : α), Subsingleton
 (C (Trunc.mk a))] → (q : Trunc α) → ((a : α) → C (Trunc.mk a)) → C q
参数：a : α；C (Trunc.mk a)；q : Trunc α；(a : α) → C (Trunc.mk a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Trunc.recOn` assuming the codomain is a `Subsingleton`.
-/
protected def recOnSubsingleton [∀ a, Subsingleton (C (mk a))] (q : Trunc α) (f : ∀ a, C (mk a)) :
    C q :=
  Trunc.rec f (fun _ b ↦ Subsingleton.elim _ (f b)) q

/-- Noncomputably extract a representative of `Trunc α` (using the axiom of choice). -/
/-
**Trunc.out** 是 Mathlib 中的一个定义，位于命名空间 `Trunc`。
形式化陈述：out : Trunc α -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputably extract a representative of `Trunc α` (using the axiom of choice).
-/
noncomputable def out : Trunc α → α :=
  Quot.out

@[simp]
/-
**Trunc.out_eq** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：out_eq (q : Trunc α) : mk q.out = q
参数：q : Trunc α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.eq`：∀ {α : Sort u_1} (a b : Trunc α), a = b
-/
theorem out_eq (q : Trunc α) : mk q.out = q :=
  Trunc.eq _ _
/-
**Trunc.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Trunc`。
形式化陈述：∀ {α : Sort u_1} (q : Trunc α), Nonempty α
参数：q : Trunc α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Trunc.exists_rep`：exists_rep (q : Trunc α) : exists a : α, mk a = q
-/
protected theorem nonempty (q : Trunc α) : Nonempty α :=
  q.exists_rep.nonempty

end Trunc

/-! ### `Quotient` with implicit `Setoid` -/


namespace Quotient

variable {γ : Sort*} {φ : Sort*} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

/-! Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `Setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules. -/

-- TODO: this whole section can probably be replaced `Quotient.mk`, with explicit parameter

/-- A version of `Quotient.mk` taking `{s : Setoid α}` as an implicit argument instead of an
/-
**Quotient.argument.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance argument. -/
/-
**Quotient.mk''** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：mk''_surjective : Function.Surjective (Quotient.mk'' : α -> Quotient s₁)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Quotient.mk` taking `{s : Setoid α}` as an implicit argument inste
ad of an
instance argument.
-/
protected abbrev mk'' (a : α) : Quotient s₁ :=
  ⟦a⟧

/-- `Quotient.mk''` is a surjective function. -/
/-
**Quotient.mk''_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Surjective Quotient.mk''
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q

--- 原说明 ---
`Quotient.mk''` is a surjective function.
-/
theorem mk''_surjective : Function.Surjective (Quotient.mk'' : α → Quotient s₁) :=
  Quot.exists_rep

/-- A version of `Quotient.liftOn` taking `{s : Setoid α}` as an implicit argument instead of an
/-
**Quotient.argument.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance argument. -/
/-
**Quotient.liftOn'** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} → {φ : Sort u_4} → {s₁ : Setoid α} → Quotient s₁ → (f : α →
 φ) → (∀ (a b : α), s₁ a b → f a = f b) → φ
参数：f : α → φ；∀ (a b : α), s₁ a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Quotient.liftOn` taking `{s : Setoid α}` as an implicit argument i
nstead of an
instance argument.
-/
protected def liftOn' (q : Quotient s₁) (f : α → φ) (h : ∀ a b, s₁ a b → f a = f b) :
    φ :=
  Quotient.liftOn q f h

@[simp]
/-
**Quotient.liftOn'_mk''** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (f : α → φ) (h : ∀ (a b : 
α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).liftOn' f h = f x
参数：f : α → φ；h : ∀ (a b : α), s₁ a b → f a = f b；x : α；Quotient.mk'' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
protected theorem liftOn'_mk'' (f : α → φ) (h) (x : α) :
    Quotient.liftOn' (@Quotient.mk'' _ s₁ x) f h = f x :=
  rfl
/-
**Quotient.surjective_liftOn'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} {f : α → φ} (h : ∀ (a b : 
α), s₁ a b → f a = f b),   (Function.Surjective fun x => x.liftOn' f h) ↔ Functi
on.Surjective f
参数：h : ∀ (a b : α), s₁ a b → f a = f b；Function.Surjective fun x => x.liftOn' f 
h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.surjective_lift`：∀ {α : Sort u_1} {γ : Sort u_4} {r : α → α → Prop}
 {f : α → γ} (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂),   Function.Surjective (
Quot.lift …
-/
@[simp] lemma surjective_liftOn' {f : α → φ} (h) :
    Function.Surjective (fun x : Quotient s₁ ↦ x.liftOn' f h) ↔ Function.Surjective f :=
  Quot.surjective_lift _

/-- A version of `Quotient.liftOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit arguments
instead of instance arguments. -/
/-
**Quotient.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {β : Sort v} → {s : Setoid α} → Quotient s → (f : α → β) → 
(∀ (a b : α), a ≈ b → f a = f b) → β
参数：f : α → β；∀ (a b : α), a ≈ b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Quotient.liftOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as impl
icit arguments
instead of instance arguments.
-/
protected def liftOn₂' (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → γ)
    (h : ∀ a₁ a₂ b₁ b₂, s₁ a₁ b₁ → s₂ a₂ b₂ → f a₁ a₂ = f b₁ b₂) : γ :=
  Quotient.liftOn₂ q₁ q₂ f h

@[simp]
/-
**Quotient.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {β : Sort v} → {s : Setoid α} → Quotient s → (f : α → β) → 
(∀ (a b : α), a ≈ b → f a = f b) → β
参数：f : α → β；∀ (a b : α), a ≈ b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem liftOn₂'_mk'' (f : α → β → γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (@Quotient.mk'' _ s₁ a) (@Quotient.mk'' _ s₂ b) f h = f a b :=
  rfl

/-- A version of `Quotient.ind` taking `{s : Setoid α}` as an implicit argument instead of an
/-
**Quotient.argument.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance argument. -/
@[elab_as_elim]
/-
**Quotient.ind'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}, (∀ (a : α), p (
Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
参数：∀ (a : α), p (Quotient.mk'' a)；q : Quotient s₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q

--- 原说明 ---
A version of `Quotient.ind` taking `{s : Setoid α}` as an implicit argument inst
ead of an
instance argument.
-/
protected theorem ind' {p : Quotient s₁ → Prop} (h : ∀ a, p (Quotient.mk'' a)) (q : Quotient s₁) :
    p q :=
  Quotient.ind h q

/-- A version of `Quotient.ind₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_elim]
/-
**Quotient.ind** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}, (∀ (a : α), mo
tive ⟦a⟧) → ∀ (q : Quotient s), motive q
参数：∀ (a : α), motive ⟦a⟧；q : Quotient s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Quotient.ind₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implici
t arguments
instead of instance arguments.
-/
protected theorem ind₂' {p : Quotient s₁ → Quotient s₂ → Prop}
    (h : ∀ a₁ a₂, p (Quotient.mk'' a₁) (Quotient.mk'' a₂))
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) : p q₁ q₂ :=
  Quotient.ind₂ h q₁ q₂

/-- A version of `Quotient.inductionOn` taking `{s : Setoid α}` as an implicit argument instead
of an instance argument. -/
@[elab_as_elim]
/-
**Quotient.inductionOn'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop} (q : Quotient s₁
), (∀ (a : α), p (Quotient.mk'' a)) → p q
参数：q : Quotient s₁；∀ (a : α), p (Quotient.mk'' a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q

--- 原说明 ---
A version of `Quotient.inductionOn` taking `{s : Setoid α}` as an implicit argum
ent instead
of an instance argument.
-/
protected theorem inductionOn' {p : Quotient s₁ → Prop} (q : Quotient s₁)
    (h : ∀ a, p (Quotient.mk'' a)) : p q :=
  Quotient.inductionOn q h

/-- A version of `Quotient.inductionOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit
arguments instead of instance arguments. -/
@[elab_as_elim]
/-
**Quotient.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} (q : Quotient s
), (∀ (a : α), motive ⟦a⟧) → motive q
参数：q : Quotient s；∀ (a : α), motive ⟦a⟧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
A version of `Quotient.inductionOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as
 implicit
arguments instead of instance arguments.
-/
protected theorem inductionOn₂' {p : Quotient s₁ → Quotient s₂ → Prop} (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (h : ∀ a₁ a₂, p (Quotient.mk'' a₁) (Quotient.mk'' a₂)) : p q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

/-- A version of `Quotient.inductionOn₃` taking `{s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}`
as implicit arguments instead of instance arguments. -/
@[elab_as_elim]
/-
**Quotient.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} (q : Quotient s
), (∀ (a : α), motive ⟦a⟧) → motive q
参数：q : Quotient s；∀ (a : α), motive ⟦a⟧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
A version of `Quotient.inductionOn₃` taking `{s₁ : Setoid α} {s₂ : Setoid β} {s₃
 : Setoid γ}`
as implicit arguments instead of instance arguments.
-/
protected theorem inductionOn₃' {p : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (q₃ : Quotient s₃)
    (h : ∀ a₁ a₂ a₃, p (Quotient.mk'' a₁) (Quotient.mk'' a₂) (Quotient.mk'' a₃)) :
    p q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

/-- A version of `Quotient.recOnSubsingleton` taking `{s₁ : Setoid α}` as an implicit argument
instead of an instance argument. -/
@[elab_as_elim]
/-
**Quotient.recOnSubsingleton'** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} →   {s₁ : Setoid α} →     {φ : Quotient s₁ → Sort u_5} →   
    [∀ (a : α), Subsingleton (φ ⟦a⟧)] → (q : Quotient s₁) → ((a : α) → φ (Quotie
nt.mk'' a)) → φ q
参数：a : α；φ ⟦a⟧；q : Quotient s₁；(a : α) → φ (Quotient.mk'' a)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
A version of `Quotient.recOnSubsingleton` taking `{s₁ : Setoid α}` as an implici
t argument
instead of an instance argument.
-/
protected def recOnSubsingleton' {φ : Quotient s₁ → Sort*} [∀ a, Subsingleton (φ ⟦a⟧)]
    (q : Quotient s₁)
    (f : ∀ a, φ (Quotient.mk'' a)) : φ q :=
  Quotient.recOnSubsingleton q f

/-- A version of `Quotient.recOnSubsingleton₂` taking `{s₁ : Setoid α} {s₂ : Setoid α}`
as implicit arguments instead of instance arguments. -/
@[elab_as_elim]
/-
**Quotient.recOnSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} →   {s : Setoid α} →     {motive : Quotient s → Sort v} →    
   [h : ∀ (a : α), Subsingleton (motive ⟦a⟧)] → (q : Quotient s) → ((a : α) → mo
tive ⟦a⟧) → motive q
参数：a : α；motive ⟦a⟧；q : Quotient s；(a : α) → motive ⟦a⟧。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Quotient.recOnSubsingleton₂` taking `{s₁ : Setoid α} {s₂ : Setoid 
α}`
as implicit arguments instead of instance arguments.
-/
protected def recOnSubsingleton₂' {φ : Quotient s₁ → Quotient s₂ → Sort*}
    [∀ a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : ∀ a₁ a₂, φ (Quotient.mk'' a₁) (Quotient.mk'' a₂)) :
    φ q₁ q₂ :=
  Quotient.recOnSubsingleton₂ q₁ q₂ f

/-- Recursion on a `Quotient` argument `a`, result type depends on `⟦a⟧`. -/
/-
**Quotient.hrecOn'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：hrecOn'_mk'' {φ : Quotient s₁ -> Sort*} (f : forall a, φ (Quotient.mk'' a)
) (c : forall a₁ a₂, a₁ ≈ a₂ -> f a₁ ≍ f a₂) (x : α) : (Quotient.mk'' x).hrecOn'
 f c = f x
参数：f : forall a, φ (Quotient.mk'' a)；c : forall a₁ a₂, a₁ ≈ a₂ -> f a₁ ≍ f a₂；x 
: α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Recursion on a `Quotient` argument `a`, result type depends on `⟦a⟧`.
-/
protected def hrecOn' {φ : Quotient s₁ → Sort*} (qa : Quotient s₁) (f : ∀ a, φ (Quotient.mk'' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ ≍ f a₂) : φ qa :=
  Quot.hrecOn qa f c

@[simp]
/-
**Quotient.hrecOn'_mk''** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s₁ : Setoid α} {φ : Quotient s₁ → Sort u_5} (f : (a : α)
 → φ (Quotient.mk'' a))   (c : ∀ (a₁ a₂ : α), a₁ ≈ a₂ → f a₁ ≍ f a₂) (x : α), (Q
uotient.mk'' x).hrecOn' f c = f x
参数：f : (a : α) → φ (Quotient.mk'' a)；c : ∀ (a₁ a₂ : α), a₁ ≈ a₂ → f a₁ ≍ f a₂；x 
: α；Quotient.mk'' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.hrecOn'`：hrecOn'_mk'' {φ : Quotient s₁ -> Sort*} (f : forall a,
 φ (Quotient.mk'' a)) (c : forall a₁ a₂, a₁ ≈ a₂ -> f a₁ ≍ f a₂) (x : α) : (Quot
ient.m…
-/
theorem hrecOn'_mk'' {φ : Quotient s₁ → Sort*} (f : ∀ a, φ (Quotient.mk'' a))
    (c : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ ≍ f a₂)
    (x : α) : (Quotient.mk'' x).hrecOn' f c = f x :=
  rfl

/-- Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` and `⟦b⟧`. -/
/-
**Quotient.hrecOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} →   {s : Setoid α} →     {motive : Quotient s → Sort v} →    
   (q : Quotient s) → (f : (a : α) → motive ⟦a⟧) → (∀ (a b : α), a ≈ b → f a ≍ f
 b) → motive q
参数：q : Quotient s；f : (a : α) → motive ⟦a⟧；∀ (a b : α), a ≈ b → f a ≍ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion on two `Quotient` arguments `a` and `b`, result type depends on `⟦a⟧` 
and `⟦b⟧`.
-/
protected def hrecOn₂' {φ : Quotient s₁ → Quotient s₂ → Sort*} (qa : Quotient s₁)
    (qb : Quotient s₂) (f : ∀ a b, φ (Quotient.mk'' a) (Quotient.mk'' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ ≍ f a₂ b₂) :
    φ qa qb :=
  Quotient.hrecOn₂ qa qb f c

@[simp]
/-
**Quotient.hrecOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} →   {s : Setoid α} →     {motive : Quotient s → Sort v} →    
   (q : Quotient s) → (f : (a : α) → motive ⟦a⟧) → (∀ (a b : α), a ≈ b → f a ≍ f
 b) → motive q
参数：q : Quotient s；f : (a : α) → motive ⟦a⟧；∀ (a b : α), a ≈ b → f a ≍ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hrecOn₂'_mk'' {φ : Quotient s₁ → Quotient s₂ → Sort*}
    (f : ∀ a b, φ (Quotient.mk'' a) (Quotient.mk'' b))
    (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ ≍ f a₂ b₂) (x : α) (qb : Quotient s₂) :
    (Quotient.mk'' x).hrecOn₂' qb f c = qb.hrecOn' (f x) fun _ _ ↦ c _ _ _ _ (Setoid.refl _) :=
  rfl

/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on quotients.
This is a version of `Quotient.map` using `Setoid.r` instead of `≈`. -/
/-
**Quotient.map'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Quotient s₁).map' 
f h = (Quotient.mk'' (f x) : Quotient s₂)
参数：f : α -> β；h；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on 
quotients.
This is a version of `Quotient.map` using `Setoid.r` instead of `≈`.
-/
protected def map' (f : α → β) (h : ∀ a b, s₁.r a b → s₂.r (f a) (f b)) :
    Quotient s₁ → Quotient s₂ :=
  Quot.map f h

@[simp]
/-
**Quotient.map'_mk''** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ : Setoid β} (f : α → β
) (h : ∀ (a b : α), s₁ a b → s₂ (f a) (f b))   (x : α), Quotient.map' f h (Quoti
ent.mk'' x) = Quotient.mk'' (f x)
参数：f : α → β；h : ∀ (a b : α), s₁ a b → s₂ (f a) (f b)；x : α；Quotient.mk'' x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem map'_mk'' (f : α → β) (h) (x : α) :
    (Quotient.mk'' x : Quotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂) :=
  rfl

/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : Quotient sa → Quotient sb → Quotient sc`. Useful to define binary operations
on quotients. This is a version of `Quotient.map₂` using `Setoid.r` instead of `≈`. -/
/-
**Quotient.map** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {sa : Setoid α} → {sb : Setoid β} 
→ (f : α → β) → (∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) → Quotient sa → Quotient sb
参数：f : α → β；∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function `f : α → β → γ` that sends equivalent elements to equivalent elem
ents
to a function `f : Quotient sa → Quotient sb → Quotient sc`. Useful to define bi
nary operations
on quotients. This is a version of `Quotient.map₂` using `Setoid.r` instead of `
≈`.
-/
protected def map₂' (f : α → β → γ)
    (h : ∀ ⦃a₁ a₂ : α⦄, s₁.r a₁ a₂ → ∀ ⦃b₁ b₂ : β⦄, s₂.r b₁ b₂ → s₃.r (f a₁ b₁) (f a₂ b₂)) :
    Quotient s₁ → Quotient s₂ → Quotient s₃ :=
  Quotient.map₂ f h

@[simp]
/-
**Quotient.map** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u_1} →   {β : Sort u_2} →     {sa : Setoid α} → {sb : Setoid β} 
→ (f : α → β) → (∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) → Quotient sa → Quotient sb
参数：f : α → β；∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂'_mk'' (f : α → β → γ) (h) (x : α) :
    (Quotient.mk'' x : Quotient s₁).map₂' f h =
      (Quotient.map' (f x) (h (Setoid.refl x)) : Quotient s₂ → Quotient s₃) :=
  rfl
/-
**Quotient.exact'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Quotient.mk'' b -> s₁
 a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
theorem exact' {a b : α} :
    (Quotient.mk'' a : Quotient s₁) = Quotient.mk'' b → s₁ a b :=
  Quotient.exact
/-
**Quotient.sound'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Quotient.mk'' b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem sound' {a b : α} : s₁ a b → @Quotient.mk'' α s₁ a = Quotient.mk'' b :=
  Quotient.sound

@[simp]
/-
**Quotient.eq'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a = Quotient.mk' 
b ↔ s₁ a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
protected theorem eq' {s₁ : Setoid α} {a b : α} :
    @Quotient.mk' α s₁ a = @Quotient.mk' α s₁ b ↔ s₁ a b :=
  Quotient.eq
/-
**Quotient.eq''** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk'' a = Quotient.mk'
' b ↔ s₁ a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
protected theorem eq'' {a b : α} : @Quotient.mk'' α s₁ a = Quotient.mk'' b ↔ s₁ a b :=
  Quotient.eq
/-
**Quotient.out_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
参数：q : Quotient s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q :=
  q.out_eq
/-
**Quotient.mk_out'** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：mk_out' (a : α) : s₁ (Quotient.mk'' a : Quotient s₁).out a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem mk_out' (a : α) : s₁ (Quotient.mk'' a : Quotient s₁).out a :=
  Quotient.exact (Quotient.out_eq _)

section

variable {s : Setoid α}

/-
**Quotient.mk''_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {s : Setoid α}, Quotient.mk'' = Quotient.mk s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
protected theorem mk''_eq_mk : Quotient.mk'' = Quotient.mk s :=
  rfl

@[simp]
/-
**Quotient.liftOn'_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {s : Setoid α} (x : α) (f : α → β) (h : ∀ 
(a b : α), s a b → f a = f b),   ⟦x⟧.liftOn' f h = f x
参数：x : α；f : α → β；h : ∀ (a b : α), s a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem liftOn'_mk (x : α) (f : α → β) (h) : (Quotient.mk s x).liftOn' f h = f x :=
  rfl

@[simp]
/-
**Quotient.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Quotient`。
形式化陈述：{α : Sort u} → {β : Sort v} → {s : Setoid α} → Quotient s → (f : α → β) → 
(∀ (a b : α), a ≈ b → f a = f b) → β
参数：f : α → β；∀ (a b : α), a ≈ b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem liftOn₂'_mk {t : Setoid β} (f : α → β → γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (Quotient.mk s a) (Quotient.mk t b) f h = f a b :=
  rfl
/-
**Quotient.map'_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quotient`。
形式化陈述：∀ {α : Sort u_1} {β : Sort u_2} {s : Setoid α} {t : Setoid β} (f : α → β) 
(h : ∀ (a b : α), s a b → t (f a) (f b))   (x : α), Quotient.map' f h ⟦x⟧ = ⟦f x
⟧
参数：f : α → β；h : ∀ (a b : α), s a b → t (f a) (f b)；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
theorem map'_mk {t : Setoid β} (f : α → β) (h) (x : α) :
    (Quotient.mk s x).map' f h = (Quotient.mk t (f x)) :=
  rfl

end

/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (q : Quotient s₁) (f : α → Prop) (h : ∀ a b, s₁ a b → f a = f b)
    [DecidablePred f] :
    Decidable (Quotient.liftOn' q f h) :=
  Quotient.lift.decidablePred _ _ q
/-
**Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α → β → Prop)
    (h : ∀ a₁ b₁ a₂ b₂, s₁ a₁ a₂ → s₂ b₁ b₂ → f a₁ b₁ = f a₂ b₂)
    [∀ a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂' q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ h _ _

end Quotient

@[simp]
/-
**Equivalence.quot_mk_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equivalence.quot_mk_eq_iff {α : Type*} {r : α -> α -> Prop} (h : Equivalen
ce r) (x y : α) : Quot.mk r x = Quot.mk r y ↔ r x y
参数：h : Equivalence r；x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
lemma Equivalence.quot_mk_eq_iff {α : Type*} {r : α → α → Prop} (h : Equivalence r) (x y : α) :
    Quot.mk r x = Quot.mk r y ↔ r x y :=
  Quotient.eq (r := ⟨r, h⟩)
