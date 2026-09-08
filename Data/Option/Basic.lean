/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Control.Combinators
public import Mathlib.Data.Option.Defs
public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Logic.Relator
public import Mathlib.Util.CompileInductive
public import Aesop
public import Batteries.Tactic.Lint.Simp

/-!
# Option of a type

This file develops the basic theory of option types.

If `α` is a type, then `Option α` can be understood as the type with one more element than `α`.
`Option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `WithBot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `Option` is a monad. We love monads.

`Part` is an alternative to `Option` that can be seen as the type of `True`/`False` values
along with a term `a : α` if the value is `True`.

-/

@[expose] public section

universe u

namespace Option

variable {α β γ δ : Type*}

/-
**Option.coe_def** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：coe_def : (fun a => ↑a : α -> Option α) = some
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_def : (fun a ↦ ↑a : α → Option α) = some :=
  rfl
/-
**Option.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：mem_map {f : α -> β} {y : β} {o : Option α} : y in o.map f ↔ exists x in o
, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_map {f : α → β} {y : β} {o : Option α} : y ∈ o.map f ↔ ∃ x ∈ o, f x = y := by simp

@[simp 1100]
/-
**Option.mem_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：mem_map_of_injective {f : α -> β} (H : Function.Injective f) {a : α} {o : 
Option α} : f a in o.map f ↔ a in o
参数：H : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {o : Option α} :
    f a ∈ o.map f ↔ a ∈ o := by
  aesop
/-
**Option.forall_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：forall_mem_map {f : α -> β} {o : Option α} {p : β -> Prop} : (forall y in 
o.map f, p y) ↔ forall x in o, p (f x)
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∀ y ∈ o.map f, p y) ↔ ∀ x ∈ o, p (f x) := by simp
/-
**Option.exists_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：exists_mem_map {f : α -> β} {o : Option α} {p : β -> Prop} : (exists y in 
o.map f, p y) ↔ exists x in o, p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∃ y ∈ o.map f, p y) ↔ ∃ x ∈ o, p (f x) := by simp
/-
**Option.coe_get** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：coe_get {o : Option α} (h : o.isSome) : ((Option.get _ h : α) : Option α) 
= o
参数：h : o.isSome。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
-/
theorem coe_get {o : Option α} (h : o.isSome) : ((Option.get _ h : α) : Option α) = o :=
  Option.some_get h
/-
**Option.eq_of_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a in o1) (h2 : a in o2) 
: o1 = o2
参数：h1 : a in o1；h2 : a in o2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a ∈ o1) (h2 : a ∈ o2) : o1 = o2 :=
  h1.trans h2.symm
/-
**Option.Mem.leftUnique** 是 Mathlib 中的一个定理，位于命名空间 `Option.Mem`。
形式化陈述：∀ {α : Type u_1}, Relator.LeftUnique fun x1 x2 => x1 ∈ x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.mem_unique`：∀ {α : Type u_1} {o : Option α} {a b : α}, a ∈ o → b 
∈ o → a = b
-/
theorem Mem.leftUnique : Relator.LeftUnique ((· ∈ ·) : α → Option α → Prop) :=
  fun _ _ _ => mem_unique
/-
**Option.some_injective** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：some_injective (α : Type*) : Function.Injective (@some α)
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
-/
theorem some_injective (α : Type*) : Function.Injective (@some α) := fun _ _ ↦ some_inj.mp

@[simp]
/-
**Option.map_comp_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_comp_some (f : α -> β) : Option.map f ∘ some = some ∘ f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_some (f : α → β) : Option.map f ∘ some = some ∘ f :=
  rfl

@[congr]
/-
**Option.bind_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：bind_congr' {f g : α -> Option β} {x y : Option α} (hx : x = y) (hf : fora
ll a in y, f a = g a) : x.bind f = y.bind g
参数：hx : x = y；hf : forall a in y, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.bind_congr`：∀ {α : Type u_1} {β : Type u_2} {o : Option α} {f g :
 α → Option β},   (∀ (a : α), o = some a → f a = g a) → o.bind f = o.bind g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bind_congr' {f g : α → Option β} {x y : Option α} (hx : x = y)
    (hf : ∀ a ∈ y, f a = g a) : x.bind f = y.bind g :=
  hx.symm ▸ bind_congr hf
/-
**Option.joinM_eq_join** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：joinM_eq_join : joinM = @join α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem joinM_eq_join : joinM = @join α :=
  funext fun _ ↦ rfl
/-
**Option.bind_eq_bind'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：bind_eq_bind' {α β : Type u} {f : α -> Option β} {x : Option α} : x >>= f 
= x.bind f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_eq_bind' {α β : Type u} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl
/-
**Option.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_coe {α β} {a : α} {f : α -> β} : f < > (a : Option α) = ↑(f a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl

@[simp]
/-
**Option.map_coe'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_coe' {a : α} {f : α -> β} : Option.map f (a : Option α) = ↑(f a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl

/-- `Option.map` as a function between functions is injective. -/
/-
**Option.map_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_injective' : Function.Injective (@Option.map α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Option.map` as a function between functions is injective.
-/
theorem map_injective' : Function.Injective (@Option.map α β) := fun f g h ↦
  funext fun x ↦ some_injective _ <| by simp only [← map_some, h]

@[simp]
/-
**Option.map_inj** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_inj {f g : α -> β} : Option.map f = Option.map g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Option.map_injective'`：map_injective' : Function.Injective (@Option.map 
α β)
-/
theorem map_inj {f g : α → β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff

@[simp]
/-
**Option.map_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_eq_id {f : α -> α} : Option.map f = id ↔ f = id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Option.map_injective'`：map_injective' : Function.Injective (@Option.map 
α β)
· 使用定理 `Option.map_id`：∀ {α : Type u_1}, Option.map id = id
-/
theorem map_eq_id {f : α → α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id
/-
**Option.map_comm** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：map_comm {f₁ : α -> β} {f₂ : α -> γ} {g₁ : β -> δ} {g₂ : γ -> δ} (h : g₁ ∘
 f₁ = g₂ ∘ f₂) (a : α) : (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂
参数：h : g₁ ∘ f₁ = g₂ ∘ f₂；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) :
    (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]

section pmap

variable {p : α → Prop} (f : ∀ a : α, p a → β) (x : Option α)

/-
**Option.mem_pmem** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：mem_pmem {a : α} (h : forall a in x, p a) (ha : a in x) : f a (h a ha) in 
pmap f x h
参数：h : forall a in x, p a；ha : a in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h := by
  rw [mem_def] at ha ⊢
  subst ha
  rfl
/-
**Option.pmap_bind** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：pmap_bind {α β γ} {x : Option α} {g : α -> Option β} {p : β -> Prop} {f : 
forall b, p b -> γ} (H) (H' : forall (a : α), forall b in g a, b in x >>= g) : p
map f (x >>= g) H = x >>= fun a => pmap f (g a) fun _ h => H _ (H' a _ h)
参数：H；H' : forall (a : α), forall b in g a, b in x >>= g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a ↦ pmap f (g a) fun _ h ↦ H _ (H' a _ h) := by
  grind [cases Option]
/-
**Option.bind_pmap** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：bind_pmap {α β γ} {p : α -> Prop} (f : forall a, p a -> β) (x : Option α) 
(g : β -> Option γ) (H) : pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h))
参数：f : forall a, p a -> β；x : Option α；g : β -> Option γ；H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h ↦ g (f a (H _ h)) := by
  grind [cases Option, pmap]

variable {f x}
/-
**Option.pbind_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：pbind_eq_none {f : forall a : α, a in x -> Option β} (h' : forall a (H : a
 in x), f a H = none -> x = none) : x.pbind f = none ↔ x = none
参数：h' : forall a (H : a in x), f a H = none -> x = none。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β}
    (h' : ∀ a (H : a ∈ x), f a H = none → x = none) : x.pbind f = none ↔ x = none := by
  grind [cases Option]
/-
**Option.join_pmap_eq_pmap_join** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：join_pmap_eq_pmap_join {f : forall a, p a -> β} {x : Option (Option α)} (H
) : (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_j
oin h) _ rfl
参数：Option α；H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h ↦ H (some a) (mem_of_mem_join h) _ rfl := by
  grind [cases Option]
/-
**Option.pmap_bind_id_eq_pmap_join** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：pmap_bind_id_eq_pmap_join {f : forall a, p a -> β} {x : Option (Option α)}
 (H) : ((pmap (pmap f) x H).bind fun a => a) = pmap f x.join fun a h => H (some 
a) (mem_of_mem_join h) _ rfl
参数：Option α；H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pmap_bind_id_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    ((pmap (pmap f) x H).bind fun a ↦ a) =
      pmap f x.join fun a h ↦ H (some a) (mem_of_mem_join h) _ rfl := by
  grind [cases Option]

end pmap

@[simp]
/-
**Option.seq_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：seq_some {α β} {a : α} {f : α -> β} : some f <*> some a = some (f a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl

@[deprecated "Use `Option.get` with proof of `isSome`." (since := "2026-01-05")]
/-
**Option.iget_mem** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} [inst : Inhabited α] {o : Option α}, o.isSome = true → o.
iget ∈ o
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iget_mem [Inhabited α] : ∀ {o : Option α}, isSome o → o.iget ∈ o
  | some _, _ => rfl

@[deprecated "Use `Option.getD`." (since := "2026-01-05")]
/-
**Option.iget_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} [inst : Inhabited α] {a : α} {o : Option α}, a ∈ o → o.ig
et = a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iget_of_mem [Inhabited α] {a : α} : ∀ {o : Option α}, a ∈ o → o.iget = a
  | _, rfl => rfl

@[deprecated "Use `Option.getD` directly." (since := "2026-01-05")]
/-
**Option.getD_default_eq_iget** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：getD_default_eq_iget [Inhabited α] (o : Option α) : o.getD default = o.ige
t
参数：o : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem getD_default_eq_iget [Inhabited α] (o : Option α) :
    o.getD default = o.iget := by cases o <;> rfl

@[simp, grind =]
/-
**Option.failure_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：failure_eq_none {α} : failure = (none : Option α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem failure_eq_none {α} : failure = (none : Option α) := rfl

@[simp]
/-
**Option.guard_eq_some'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：guard_eq_some' {p : Prop} [Decidable p] (u) : _root_.guard p = some u ↔ p
参数：u。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : _root_.guard p = some u ↔ p := by
  grind [cases Option, _root_.guard]

/-- Given an element of `a : Option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
/-
**Option.casesOn'** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f = x
参数：x : β；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element of `a : Option α`, a default element `b : β` and a function `α 
→ β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise.
-/
def casesOn' : Option α → β → (α → β) → β
  | none, n, _ => n
  | some a, _, s => s a

@[simp]
/-
**Option.casesOn'_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (x : β) (f : α → β), none.casesOn' x f = x
参数：x : β；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
-/
theorem casesOn'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl

@[simp]
/-
**Option.casesOn'_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (x : β) (f : α → β) (a : α), (some a).case
sOn' x f = f a
参数：x : β；f : α → β；a : α；some a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
-/
theorem casesOn'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl

@[simp]
/-
**Option.casesOn'_coe** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (x : β) (f : α → β) (a : α), (some a).case
sOn' x f = f a
参数：x : β；f : α → β；a : α；some a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
-/
theorem casesOn'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl

@[simp]
/-
**Option.casesOn'_none_coe** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : Option α → β) (o : Option α), o.cases
On' (f none) (f ∘ fun a => some a) = f o
参数：f : Option α → β；o : Option α；f none；f ∘ fun a => some a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem casesOn'_none_coe (f : Option α → β) (o : Option α) :
    casesOn' o (f none) (f ∘ (fun a ↦ ↑a)) = f o := by cases o <;> rfl
/-
**Option.casesOn'_eq_elim** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (b : β) (f : α → β) (a : Option α), a.case
sOn' b f = a.elim b f
参数：b : β；f : α → β；a : Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.casesOn'`：casesOn'_none (x : β) (f : α -> β) : casesOn' none x f 
= x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma casesOn'_eq_elim (b : β) (f : α → β) (a : Option α) :
    Option.casesOn' a b f = Option.elim a b f := by cases a <;> rfl
/-
**Option.orElse_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：orElse_eq_some (o o' : Option α) (x : α) : (o <|> o') = some x ↔ o = some 
x ∨ o = none ∧ o' = some x
参数：o o' : Option α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.orElse_eq_or`：∀ {α : Type u_1} {o : Option α} {f : Unit → Option 
α}, o.orElse f = o.or (f ())
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orElse_eq_some (o o' : Option α) (x : α) :
    (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x := by
  simp
/-
**Option.orElse_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：orElse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = non
e
参数：o o' : Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.orElse_eq_or`：∀ {α : Type u_1} {o : Option α} {f : Unit → Option 
α}, o.orElse f = o.or (f ())
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orElse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none := by
  simp

section

/-
**Option.choice_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：choice_eq_none (α : Type*) [IsEmpty α] : choice α = none
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.choice_eq_none_iff_not_nonempty`：∀ {α : Type u_1}, Option.choice 
α = none ↔ ¬Nonempty α
· 使用定理 `not_nonempty_iff_imp_false`：not_nonempty_iff_imp_false {α : Sort*} : ¬No
nempty α ↔ α -> False
-/
theorem choice_eq_none (α : Type*) [IsEmpty α] : choice α = none :=
  choice_eq_none_iff_not_nonempty.mpr (not_nonempty_iff_imp_false.mpr isEmptyElim)

end

@[simp]
/-
**Option.elim_none_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：elim_none_some (f : Option α -> β) (i : Option α) : i.elim (f none) (f ∘ s
ome) = f i
参数：f : Option α -> β；i : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem elim_none_some (f : Option α → β) (i : Option α) : i.elim (f none) (f ∘ some) = f i := by
  cases i <;> rfl
/-
**Option.elim_comp** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：elim_comp (h : α -> β) {f : γ -> α} {x : α} {i : Option γ} : (i.elim (h x)
 fun j => h (f j)) = h (i.elim x f)
参数：h : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem elim_comp (h : α → β) {f : γ → α} {x : α} {i : Option γ} :
    (i.elim (h x) fun j => h (f j)) = h (i.elim x f) := by cases i <;> rfl
/-
**Option.elim_comp** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：elim_comp (h : α -> β) {f : γ -> α} {x : α} {i : Option γ} : (i.elim (h x)
 fun j => h (f j)) = h (i.elim x f)
参数：h : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem elim_comp₂ (h : α → β → γ) {f : γ → α} {x : α} {g : γ → β} {y : β}
    {i : Option γ} : (i.elim (h x y) fun j => h (f j) (g j)) = h (i.elim x f) (i.elim y g) := by
  cases i <;> rfl
/-
**Option.elim_apply** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：elim_apply {f : γ -> α -> β} {x : α -> β} {i : Option γ} {y : α} : i.elim 
x f y = i.elim (x y) fun j => f j y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.elim_comp`：elim_comp (h : α -> β) {f : γ -> α} {x : α} {i : Optio
n γ} : (i.elim (h x) fun j => h (f j)) = h (i.elim x f)
-/
theorem elim_apply {f : γ → α → β} {x : α → β} {i : Option γ} {y : α} :
    i.elim x f y = i.elim (x y) fun j => f j y := by rw [elim_comp fun f : α → β => f y]

open Function in
@[simp]
/-
**Option.elim'_update** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : DecidableEq α] (f : β) (g : α → β)
 (a : α) (x : β),   Option.elim' f (Function.update g a x) = Function.update (Op
tion.elim' f g) (some a) x
参数：f : β；g : α → β；a : α；x : β；Function.update g a x；Option.elim' f g；some a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.rec_update`：rec_update {ι κ : Sort*} {α : κ -> Sort*} [Decidabl
eEq ι] [DecidableEq κ] {ctor : ι -> κ} (_ : Function.Injective ctor) (recursor :
 ((i : ι)…
· 使用定理 `Option.some.inj`：∀ {α : Type u} {val val_1 : α}, some val = some val_1 →
 val = val_1
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
-/
lemma elim'_update {α : Type*} {β : Type*} [DecidableEq α]
    (f : β) (g : α → β) (a : α) (x : β) :
    Option.elim' f (update g a x) = update (Option.elim' f g) (some a) x :=
  -- Can't reuse `Option.rec_update` as `Option.elim'` is not defeq.
  Function.rec_update (α := fun _ => β) (@Option.some.inj _) (Option.elim' f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

@[simp]
/-
**Option.getD_comp_some** 是 Mathlib 中的一个引理，位于命名空间 `Option`。
形式化陈述：getD_comp_some (d : α) : (fun x => x.getD d) ∘ some = id
参数：d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma getD_comp_some (d : α) : (fun x ↦ x.getD d) ∘ some = id := by
  ext
  simp only [Function.comp_apply, getD_some, id_eq]

@[simp]
/-
**Option.none_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：none_eq_map_iff {x : Option α} {f : α -> β} : none = x.map f ↔ x = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Option.map_eq_none_iff`：∀ {α : Type u_1} {x : Option α} {α_1 : Type u_2}
 {f : α → α_1}, Option.map f x = none ↔ x = none
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem none_eq_map_iff {x : Option α} {f : α → β} : none = x.map f ↔ x = none := by
  rw [eq_comm, map_eq_none_iff]

@[simp]
/-
**Option.some_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：some_eq_map_iff {b : β} {x : Option α} {f : α -> β} : some b = x.map f ↔ e
xists (a : α), x = some a ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Option.map_eq_some_iff`：∀ {α : Type u_1} {b : α} {α_1 : Type u_2} {x : O
ption α_1} {f : α_1 → α},   Option.map f x = some b ↔ ∃ a, x = some a ∧ f a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem some_eq_map_iff {b : β} {x : Option α} {f : α → β} :
    some b = x.map f ↔ ∃ (a : α), x = some a ∧ f a = b := by
  rw [eq_comm, map_eq_some_iff]

end Option

