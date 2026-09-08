/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.Simps.Basic

/-!
# Subtypes

This file provides basic API for subtypes, which are defined in core.

A subtype is a type made from restricting another type, say `α`, to its elements that satisfy some
predicate, say `p : α → Prop`. Specifically, it is the type of pairs `⟨val, property⟩` where
`val : α` and `property : p val`. It is denoted `Subtype p` and notation `{val : α // p val}` is
available.

A subtype has a natural coercion to the parent type, by coercing `⟨val, property⟩` to `val`. As
such, subtypes can be thought of as bundled sets, the difference being that elements of a set are
still of type `α` while elements of a subtype aren't.
-/

@[expose] public section


open Function

namespace Subtype

variable {α β γ : Sort*} {p q : α → Prop}

attribute [coe] Subtype.val

initialize_simps_projections Subtype (val → coe)

/-- A version of `x.property` or `x.2` where `p` is syntactically applied to the coercion of `x`
  instead of `x.1`. A similar result is `Subtype.mem` in `Mathlib/Data/Set/Basic.lean`. -/
-- This is a leftover from Lean 3: it is identical to `Subtype.property`, and should be deprecated.
/-
**Subtype.prop** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：prop (x : Subtype p) : p x
参数：x : Subtype p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem prop (x : Subtype p) : p x :=
  x.2

/-- An alternative version of `Subtype.forall`. This one is useful if Lean cannot figure out `q`
  when using `Subtype.forall` from right to left. -/
/-
**Subtype.forall'** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Prop}, (∀ (x : α) (h 
: p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
参数：x : α；∀ (x : α) (h : p x), q x h；x : { a // p a }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩

--- 原说明 ---
An alternative version of `Subtype.forall`. This one is useful if Lean cannot fi
gure out `q`
  when using `Subtype.forall` from right to left.
-/
protected theorem forall' {q : ∀ x, p x → Prop} : (∀ x h, q x h) ↔ ∀ x : { a // p a }, q x x.2 :=
  (@Subtype.forall _ _ fun x ↦ q x.1 x.2).symm

/-- An alternative version of `Subtype.exists`. This one is useful if Lean cannot figure out `q`
  when using `Subtype.exists` from right to left. -/
/-
**Subtype.exists'** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Prop}, (∃ x, ∃ (h : p
 x), q x h) ↔ ∃ x, q ↑x ⋯
参数：x : α；∃ x, ∃ (h : p x), q x h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩

--- 原说明 ---
An alternative version of `Subtype.exists`. This one is useful if Lean cannot fi
gure out `q`
  when using `Subtype.exists` from right to left.
-/
protected theorem exists' {q : ∀ x, p x → Prop} : (∃ x h, q x h) ↔ ∃ x : { a // p a }, q x x.2 :=
  (@Subtype.exists _ _ fun x ↦ q x.1 x.2).symm
/-
**Subtype.heq_iff_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：heq_iff_coe_eq (h : forall x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // 
q x }} : a1 ≍ a2 ↔ (a1 : α) = (a2 : α)
参数：h : forall x, p x ↔ q x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem heq_iff_coe_eq (h : ∀ x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }} :
    a1 ≍ a2 ↔ (a1 : α) = (a2 : α) :=
  Eq.rec
    (motive := fun (pp : (α → Prop)) _ ↦ ∀ a2' : {x // pp x}, a1 ≍ a2' ↔ (a1 : α) = (a2' : α))
    (by grind) (funext <| fun x ↦ propext (h x)) a2
/-
**Subtype.heq_iff_coe_heq** 是 Mathlib 中的一个引理，位于命名空间 `Subtype`。
形式化陈述：heq_iff_coe_heq {α β : Sort _} {p : α -> Prop} {q : β -> Prop} {a : {x // 
p x}} {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍ b ↔ (a : α) ≍ (b : β)
参数：h : α = β；h' : p ≍ q。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma heq_iff_coe_heq {α β : Sort _} {p : α → Prop} {q : β → Prop} {a : {x // p x}}
    {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍ b ↔ (a : α) ≍ (b : β) := by grind

@[simp]
/-
**Subtype.coe_eta** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
参数：a : { a // p a }；h : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
  Subtype.ext rfl
/-
**Subtype.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_mk (a h) : (@mk α p a h : α) = a
参数：a h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (a h) : (@mk α p a h : α) = a :=
  rfl

/-- Restatement of `Subtype.mk.injEq` as an iff. -/
/-
**Subtype.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Restatement of `Subtype.mk.injEq` as an iff.
-/
theorem mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' := by simp
/-
**Subtype.coe_eq_of_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h : ↑a = b) : a = ⟨b, h ▸ a.2⟩
参数：h : ↑a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h : ↑a = b) : a = ⟨b, h ▸ a.2⟩ :=
  Subtype.ext h
/-
**Subtype.coe_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_eq_iff {a : { a // p a }} {b : α} : ↑a = b ↔ exists h, a = ⟨b, h⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eq_iff {a : { a // p a }} {b : α} : ↑a = b ↔ ∃ h, a = ⟨b, h⟩ := by grind
/-
**Subtype.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_injective : Injective (fun (a : Subtype p) => (a : α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem coe_injective : Injective (fun (a : Subtype p) ↦ (a : α)) := fun _ _ ↦ Subtype.ext
/-
**Subtype.val_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop}, Function.Injective Subtype.val
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
@[simp] theorem val_injective : Injective (@val _ p) :=
  coe_injective
/-
**Subtype.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b :=
  coe_injective.eq_iff
/-
**Subtype.val_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
-/
theorem val_inj {a b : Subtype p} : a.val = b.val ↔ a = b :=
  coe_inj
/-
**Subtype.coe_ne_coe** 是 Mathlib 中的一个引理，位于命名空间 `Subtype`。
形式化陈述：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma coe_ne_coe {a b : Subtype p} : (a : α) ≠ b ↔ a ≠ b := coe_injective.ne_iff

@[simp]
/-
**Subtype._root_.exists_eq_subtype_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.exists_eq_subtype_mk_iff {a : Subtype p} {b : α} :
    (∃ h : p b, a = Subtype.mk b h) ↔ ↑a = b :=
  coe_eq_iff.symm

@[simp]
/-
**Subtype._root_.exists_subtype_mk_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.exists_subtype_mk_eq_iff {a : Subtype p} {b : α} :
    (∃ h : p b, Subtype.mk b h = a) ↔ b = a := by grind
/-
**Subtype._root_.Function.extend_val_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.extend_val_apply {p : β → Prop} {g : {x // p x} → γ} {j : β → γ}
    {b : β} (hb : p b) : val.extend g j b = g ⟨b, hb⟩ :=
  val_injective.extend_apply g j ⟨b, hb⟩
/-
**Subtype._root_.Function.extend_val_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.extend_val_apply' {p : β → Prop} {g : {x // p x} → γ} {j : β → γ}
    {b : β} (hb : ¬p b) : val.extend g j b = j b := by
  grind [Function.extend]

/-- Restrict a (dependent) function to a subtype -/
/-
**Subtype.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Subtype`。
形式化陈述：restrict {α} {β : α -> Type*} (p : α -> Prop) (f : forall x, β x) (x : Sub
type p) : β x.1
参数：p : α -> Prop；f : forall x, β x；x : Subtype p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a (dependent) function to a subtype
-/
def restrict {α} {β : α → Type*} (p : α → Prop) (f : ∀ x, β x) (x : Subtype p) : β x.1 :=
  f x

@[simp, grind =]
/-
**Subtype.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：restrict_apply {α} {β : α -> Type*} (f : forall x, β x) (p : α -> Prop) (x
 : Subtype p) : restrict p f x = f x.1
参数：f : forall x, β x；p : α -> Prop；x : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_apply {α} {β : α → Type*} (f : ∀ x, β x) (p : α → Prop) (x : Subtype p) :
    restrict p f x = f x.1 := by
  rfl
/-
**Subtype.restrict_def** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：restrict_def {α β} (f : α -> β) (p : α -> Prop) : restrict p f = f ∘ (fun 
(a : Subtype p) => a)
参数：f : α -> β；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_def {α β} (f : α → β) (p : α → Prop) :
    restrict p f = f ∘ (fun (a : Subtype p) ↦ a) := rfl
/-
**Subtype.restrict_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：restrict_injective {α β} {f : α -> β} (p : α -> Prop) (h : Injective f) : 
Injective (restrict p f)
参数：p : α -> Prop；h : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem restrict_injective {α β} {f : α → β} (p : α → Prop) (h : Injective f) :
    Injective (restrict p f) :=
  h.comp coe_injective
/-
**Subtype.surjective_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：surjective_restrict {α} {β : α -> Type*} [ne : forall a, Nonempty (β a)] (
p : α -> Prop) : Surjective fun f : forall x, β x => restrict p f
参数：β a；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_restrict {α} {β : α → Type*} [ne : ∀ a, Nonempty (β a)] (p : α → Prop) :
    Surjective fun f : ∀ x, β x ↦ restrict p f := by
  classical
  exact fun f ↦ ⟨fun x ↦ if h : p x then f ⟨x, h⟩ else Nonempty.some (ne x), by grind⟩

/-- Defining a map into a subtype, this can be seen as a "coinduction principle" of `Subtype` -/
@[simps]
/-
**Subtype.coind** 是 Mathlib 中的一个定义，位于命名空间 `Subtype`。
形式化陈述：coind {α β} (f : α -> β) {p : β -> Prop} (h : forall a, p (f a)) : α -> Su
btype p
参数：f : α -> β；h : forall a, p (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining a map into a subtype, this can be seen as a "coinduction principle" of 
`Subtype`
-/
def coind {α β} (f : α → β) {p : β → Prop} (h : ∀ a, p (f a)) : α → Subtype p := fun a ↦ ⟨f a, h a⟩
/-
**Subtype.coind_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coind_injective {α β} {f : α -> β} {p : β -> Prop} (h : forall a, p (f a))
 (hf : Injective f) : Injective (coind f h)
参数：h : forall a, p (f a)；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coind_injective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) (hf : Injective f) :
    Injective (coind f h) := fun x y hxy ↦ hf <| by apply congr_arg Subtype.val hxy
/-
**Subtype.coind_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_4} {β : Sort u_5} {f : α → β} {p : β → Prop} (h : ∀ (a : α),
 p (f a)),   Function.Injective (Subtype.coind f h) ↔ Function.Injective f
参数：h : ∀ (a : α), p (f a)；Subtype.coind f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.coind_injective`：coind_injective {α β} {f : α -> β} {p : β -> Pr
op} (h : forall a, p (f a)) (hf : Injective f) : Injective (coind f h)
-/
@[simp] theorem coind_injective_iff {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a)) :
    Injective (coind f h) ↔ Injective f :=
  ⟨Subtype.coe_injective.comp, coind_injective h⟩

/-- Restriction of a function to a function on subtypes. -/
@[simps]
/-
**Subtype.map** 是 Mathlib 中的一个定义，位于命名空间 `Subtype`。
形式化陈述：map {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall a, p a -> q (
f a)) : Subtype p -> Subtype q
参数：f : α -> β；h : forall a, p a -> q (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a function to a function on subtypes.
-/
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ a, p a → q (f a)) :
    Subtype p → Subtype q :=
  fun x ↦ ⟨f x, h x x.prop⟩
/-
**Subtype.map_def** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_def {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall a, p a ->
 q (f a)) : map f h = fun x => ⟨f x, h x x.prop⟩
参数：f : α -> β；h : forall a, p a -> q (f a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_def {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ a, p a → q (f a)) :
    map f h = fun x ↦ ⟨f x, h x x.prop⟩ :=
  rfl
/-
**Subtype.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_comp {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} {x : Subtype p} (
f : α -> β) (h : forall a, p a -> q (f a)) (g : β -> γ) (l : forall a, q a -> r 
(g a)) : map g l (map f h x) = map (g ∘ f) (fun a ha => l (f a) <| h a ha) x
参数：f : α -> β；h : forall a, p a -> q (f a)；g : β -> γ；l : forall a, q a -> r (g 
a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : Subtype p}
    (f : α → β) (h : ∀ a, p a → q (f a)) (g : β → γ) (l : ∀ a, q a → r (g a)) :
    map g l (map f h x) = map (g ∘ f) (fun a ha ↦ l (f a) <| h a ha) x :=
  rfl
/-
**Subtype.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_id {p : α -> Prop} {h : forall a, p a -> p (id a)} : map (@id α) h = i
d
参数：id a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_id {p : α → Prop} {h : ∀ a, p a → p (id a)} : map (@id α) h = id :=
  funext fun _ ↦ rfl
/-
**Subtype.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_injective {p : α -> Prop} {q : β -> Prop} {f : α -> β} (h : forall a, 
p a -> q (f a)) (hf : Injective f) : Injective (map f h)
参数：h : forall a, p a -> q (f a)；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coind_injective`：coind_injective {α β} {f : α -> β} {p : β -> Pr
op} (h : forall a, p (f a)) (hf : Injective f) : Injective (coind f h)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem map_injective {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a, p a → q (f a))
    (hf : Injective f) : Injective (map f h) :=
  coind_injective _ <| hf.comp coe_injective
/-
**Subtype.map_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_involutive {p : α -> Prop} {f : α -> α} (h : forall a, p a -> p (f a))
 (hf : Involutive f) : Involutive (map f h)
参数：h : forall a, p a -> p (f a)；hf : Involutive f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem map_involutive {p : α → Prop} {f : α → α} (h : ∀ a, p a → p (f a))
    (hf : Involutive f) : Involutive (map f h) :=
  fun x ↦ Subtype.ext (hf x)
/-
**Subtype.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_eq {p : α -> Prop} {q : β -> Prop} {f g : α -> β} (h₁ : forall a : α, 
p a -> q (f a)) (h₂ : forall a : α, p a -> q (g a)) {x y : Subtype p} : map f h₁
 x = map g h₂ y ↔ f x = g y
参数：h₁ : forall a : α, p a -> q (f a)；h₂ : forall a : α, p a -> q (g a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem map_eq {p : α → Prop} {q : β → Prop} {f g : α → β}
    (h₁ : ∀ a : α, p a → q (f a)) (h₂ : ∀ a : α, p a → q (g a))
    {x y : Subtype p} :
    map f h₁ x = map g h₂ y ↔ f x = g y :=
  Subtype.ext_iff
/-
**Subtype.map_ne** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：map_ne {p : α -> Prop} {q : β -> Prop} {f g : α -> β} (h₁ : forall a : α, 
p a -> q (f a)) (h₂ : forall a : α, p a -> q (g a)) {x y : Subtype p} : map f h₁
 x != map g h₂ y ↔ f x != g y
参数：h₁ : forall a : α, p a -> q (f a)；h₂ : forall a : α, p a -> q (g a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Subtype.map_eq`：map_eq {p : α -> Prop} {q : β -> Prop} {f g : α -> β} (h
₁ : forall a : α, p a -> q (f a)) (h₂ : forall a : α, p a -> q (g a)) {x y : Sub
type…
-/
theorem map_ne {p : α → Prop} {q : β → Prop} {f g : α → β}
    (h₁ : ∀ a : α, p a → q (f a)) (h₂ : ∀ a : α, p a → q (g a))
    {x y : Subtype p} :
    map f h₁ x ≠ map g h₂ y ↔ f x ≠ g y :=
  map_eq h₁ h₂ |>.not
/-
**Subtype.** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasEquiv α] (p : α → Prop) : HasEquiv (Subtype p) :=
  ⟨fun s t ↦ (s : α) ≈ (t : α)⟩
/-
**Subtype.equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：equiv_iff [HasEquiv α] {p : α -> Prop} {s t : Subtype p} : s ≈ t ↔ (s : α)
 ≈ (t : α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem equiv_iff [HasEquiv α] {p : α → Prop} {s t : Subtype p} : s ≈ t ↔ (s : α) ≈ (t : α) :=
  Iff.rfl

variable [Setoid α]
/-
**Subtype.refl** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} [inst : Setoid α] (s : Subtype p), s ≈ s
参数：s : Subtype p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
protected theorem refl (s : Subtype p) : s ≈ s :=
  Setoid.refl _
/-
**Subtype.symm** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} [inst : Setoid α] {s t : Subtype p}, s ≈ t
 → t ≈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
protected theorem symm {s t : Subtype p} (h : s ≈ t) : t ≈ s :=
  Setoid.symm h
/-
**Subtype.trans** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：∀ {α : Sort u_1} {p : α → Prop} [inst : Setoid α] {s t u : Subtype p}, s ≈
 t → t ≈ u → s ≈ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
-/
protected theorem trans {s t u : Subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
  Setoid.trans h₁ h₂
/-
**Subtype.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：equivalence (p : α -> Prop) : Equivalence (@HasEquiv.Equiv (Subtype p) _)
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.refl`：∀ {α : Sort u_1} {p : α → Prop} [inst : Setoid α] (s : Sub
type p), s ≈ s
· 使用定理 `Subtype.symm`：∀ {α : Sort u_1} {p : α → Prop} [inst : Setoid α] {s t : S
ubtype p}, s ≈ t → t ≈ s
· 使用定理 `Subtype.trans`：∀ {α : Sort u_1} {p : α → Prop} [inst : Setoid α] {s t u 
: Subtype p}, s ≈ t → t ≈ u → s ≈ u
-/
theorem equivalence (p : α → Prop) : Equivalence (@HasEquiv.Equiv (Subtype p) _) :=
  .mk (Subtype.refl) (@Subtype.symm _ p _) (@Subtype.trans _ p _)
/-
**Subtype.** 是 Mathlib 中的一个实例，位于命名空间 `Subtype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : α → Prop) : Setoid (Subtype p) :=
  Setoid.mk (· ≈ ·) (equivalence p)

end Subtype

namespace Subtype

/-! Some facts about sets, which require that `α` is a type. -/
variable {α : Type*}

@[simp]
/-
**Subtype.coe_prop** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
参数：a : { a // a in S }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_prop {S : Set α} (a : { a // a ∈ S }) : ↑a ∈ S :=
  a.prop
/-
**Subtype.val_prop** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：val_prop {S : Set α} (a : { a // a in S }) : a.val in S
参数：a : { a // a in S }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem val_prop {S : Set α} (a : { a // a ∈ S }) : a.val ∈ S :=
  a.prop

end Subtype

