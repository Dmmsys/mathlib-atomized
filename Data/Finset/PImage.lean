/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.PFun
public import Mathlib.Data.Part

/-!
# Image of a `Finset α` under a partially defined function

In this file we define `Part.toFinset` and `Finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/

@[expose] public section


variable {α β : Type*}

namespace Part

/-- Convert an `o : Part α` with decidable `Part.Dom o` to `Finset α`. -/
/-
**Part.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：toFinset (o : Part α) [Decidable o.Dom] : Finset α
参数：o : Part α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert an `o : Part α` with decidable `Part.Dom o` to `Finset α`.
-/
def toFinset (o : Part α) [Decidable o.Dom] : Finset α :=
  o.toOption.toFinset

@[simp]
/-
**Part.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} : x in o.toFinset ↔ x 
in o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} : x ∈ o.toFinset ↔ x ∈ o := by
  simp [toFinset]

@[simp]
/-
**Part.toFinset_none** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：toFinset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finse
t α)
参数：none : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.none_toOption`：none_toOption [Decidable (@none α).Dom] : (none : Pa
rt α).toOption = Option.none
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) := by
  simp [toFinset]

@[simp]
/-
**Part.toFinset_some** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：toFinset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a}
参数：some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.some_toOption`：some_toOption (a : α) [Decidable (some a).Dom] : (so
me a).toOption = Option.some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} := by
  simp [toFinset]

@[simp]
/-
**Part.coe_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x |
 x in o }
参数：o : Part α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Part.mem_toFinset`：mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} :
 x in o.toFinset ↔ x in o
-/
theorem coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x | x ∈ o } :=
  Set.ext fun _ => mem_toFinset

end Part

namespace Finset

variable [DecidableEq β] {f g : α →. β} [∀ x, Decidable (f x).Dom] [∀ x, Decidable (g x).Dom]
  {s t : Finset α} {b : β}

/-- Image of `s : Finset α` under a partially defined function `f : α →. β`. -/
/-
**Finset.pimage** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：pimage (f : α ->. β) [forall x, Decidable (f x).Dom] (s : Finset α) : Fins
et β
参数：f : α ->. β；f x；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image of `s : Finset α` under a partially defined function `f : α →. β`.
-/
def pimage (f : α →. β) [∀ x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.biUnion fun x => (f x).toFinset

@[simp]
/-
**Finset.mem_pimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_pimage : b in s.pimage f ↔ exists a in s, b in f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [pimage]

@[simp, norm_cast]
/-
**Finset.coe_pimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_pimage : (s.pimage f : Set β) = f.image s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_pimage`：mem_pimage : b in s.pimage f ↔ exists a in s, b in f 
a
-/
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun _ => mem_pimage

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finset.pimage_some** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_some (s : Finset α) (f : α -> β) [forall x, Decidable (Part.some <|
 f x).Dom] : (s.pimage fun x => Part.some (f x)) = s.image f
参数：s : Finset α；f : α -> β；Part.some <| f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f := by
  ext
  simp [eq_comm]
/-
**Finset.pimage_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_congr (h₁ : s = t) (h₂ : forall x in t, f x = g x) : s.pimage f = t
.pimage g
参数：h₁ : s = t；h₂ : forall x in t, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g := by
  aesop

/-- Rewrite `s.pimage f` in terms of `Finset.filter`, `Finset.attach`, and `Finset.image`. -/
/-
**Finset.pimage_eq_image_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_eq_image_filter : s.pimage f = {x in s | (f x).Dom}.attach.image fu
n x : { x // x in filter (fun x => (f x).Dom) s } => (f x).get (mem_filter.mp x.
coe_prop).2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
Rewrite `s.pimage f` in terms of `Finset.filter`, `Finset.attach`, and `Finset.i
mage`.
-/
theorem pimage_eq_image_filter : s.pimage f =
    {x ∈ s | (f x).Dom}.attach.image
      fun x : { x // x ∈ filter (fun x => (f x).Dom) s } =>
        (f x).get (mem_filter.mp x.coe_prop).2 := by
  aesop (add simp Part.mem_eq)
/-
**Finset.pimage_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_union [DecidableEq α] : (s union t).pimage f = s.pimage f union t.p
image f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_pimage`：coe_pimage : (s.pimage f : Set β) = f.image s
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1 <| by
  simp only [coe_pimage, coe_union, ← PFun.image_union]

@[simp]
/-
**Finset.pimage_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_empty : pimage f ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pimage_empty : pimage f ∅ = ∅ := by
  ext
  simp
/-
**Finset.pimage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_subset {t : Finset β} : s.pimage f subseteq t ↔ forall x in s, fora
ll y in f x, y in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x ∈ s, ∀ y ∈ f x, y ∈ t := by
  simp [subset_iff, @forall_comm _ β]

@[gcongr, mono]
/-
**Finset.pimage_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_mono (h : s subseteq t) : s.pimage f subseteq t.pimage f
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.pimage_subset`：pimage_subset {t : Finset β} : s.pimage f subseteq
 t ↔ forall x in s, forall y in f x, y in t
· 使用定理 `Finset.mem_pimage`：mem_pimage : b in s.pimage f ↔ exists a in s, b in f 
a
-/
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2 fun x hx _ hy => mem_pimage.2 ⟨x, h hx, hy⟩
/-
**Finset.pimage_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pimage_inter [DecidableEq α] : (s inter t).pimage f subseteq s.pimage f in
ter t.pimage f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_pimage`：coe_pimage : (s.pimage f : Set β) = f.image s
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
-/
theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]

end Finset

