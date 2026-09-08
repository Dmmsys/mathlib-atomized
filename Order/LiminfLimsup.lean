/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Order.Hom.CompleteLattice

/-!
# liminfs and limsups of functions and filters

Defines the liminf/limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `limsSup f` (`limsInf f`) where `f` is a filter taking values in a conditionally complete
lattice. `limsSup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`limsInf f`). To work with the Limsup along a function `u` use `limsSup (map u f)`.

Usually, one defines the Limsup as `inf (sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `inf_n (sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `limsup (fun x ↦ 1/x)` on ℝ).
Then there is no guarantee that the quantity above really decreases (the value of the `sup`
beforehand is not really well defined, as one cannot use ∞), so that the Inf could be anything.
So one cannot use this `inf sup ...` definition in conditionally complete lattices, and one has
to use a less tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/

@[expose] public section

open Filter Set Function

variable {α β γ ι ι' : Type*}

namespace Filter

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s : Set α} {u : β → α}

/-- The `limsSup` of a filter `f` is the infimum of the `a` such that the inequality
`x ≤ a` eventually holds for `f`. -/
/-
**Filter.limsSup** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：limsSup (f : Filter α) : α
参数：f : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `limsSup` of a filter `f` is the infimum of the `a` such that the inequality
`x ≤ a` eventually holds for `f`.
-/
def limsSup (f : Filter α) : α :=
  sInf { a | ∀ᶠ n in f, n ≤ a }

/-- The `limsInf` of a filter `f` is the supremum of the `a` such that the inequality
`x ≥ a` eventually holds for `f`. -/
/-
**Filter.limsInf** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：limsInf (f : Filter α) : α
参数：f : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `limsInf` of a filter `f` is the supremum of the `a` such that the inequalit
y
`x ≥ a` eventually holds for `f`.
-/
def limsInf (f : Filter α) : α :=
  sSup { a | ∀ᶠ n in f, a ≤ n }

/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that
the inequality `u x ≤ a` eventually holds for `f`. -/
/-
**Filter.limsup** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：limsup (u : β -> α) (f : Filter β) : α
参数：u : β -> α；f : Filter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such
 that
the inequality `u x ≤ a` eventually holds for `f`.
-/
def limsup (u : β → α) (f : Filter β) : α :=
  limsSup (map u f)

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that
the inequality `u x ≥ a` eventually holds for `f`. -/
/-
**Filter.liminf** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：liminf (u : β -> α) (f : Filter β) : α
参数：u : β -> α；f : Filter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `liminf` of a function `u` along a filter `f` is the supremum of the `a` suc
h that
the inequality `u x ≥ a` eventually holds for `f`.
-/
def liminf (u : β → α) (f : Filter β) : α :=
  limsInf (map u f)

/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that the inequality `u x ≤ a` eventually holds for `f`, whenever `p x` holds. -/
/-
**Filter.blimsup** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：blimsup (u : β -> α) (f : Filter β) (p : β -> Prop)
参数：u : β -> α；f : Filter β；p : β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, 
is the infimum
of the `a` such that the inequality `u x ≤ a` eventually holds for `f`, whenever
 `p x` holds.
-/
def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  sInf { a | ∀ᶠ x in f, p x → u x ≤ a }

/-- The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, is the supremum
of the `a` such that the inequality `a ≤ u x` eventually holds for `f` whenever `p x` holds. -/
/-
**Filter.bliminf** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：bliminf (u : β -> α) (f : Filter β) (p : β -> Prop)
参数：u : β -> α；f : Filter β；p : β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, 
is the supremum
of the `a` such that the inequality `a ≤ u x` eventually holds for `f` whenever 
`p x` holds.
-/
def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sSup { a | ∀ᶠ x in f, p x → a ≤ u x }

section

variable {f : Filter β} {u : β → α} {p : β → Prop}

/-
**Filter.limsup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_eq : limsup u f = sInf { a | forallᶠ n in f, u n <= a }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limsup_eq : limsup u f = sInf { a | ∀ᶠ n in f, u n ≤ a } :=
  rfl
/-
**Filter.liminf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_eq : liminf u f = sSup { a | forallᶠ n in f, a <= u n }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liminf_eq : liminf u f = sSup { a | ∀ᶠ n in f, a ≤ u n } :=
  rfl
/-
**Filter.blimsup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_eq : blimsup u f p = sInf { a | forallᶠ x in f, p x -> u x <= a }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blimsup_eq : blimsup u f p = sInf { a | ∀ᶠ x in f, p x → u x ≤ a } :=
  rfl
/-
**Filter.bliminf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_eq : bliminf u f p = sSup { a | forallᶠ x in f, p x -> a <= u x }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bliminf_eq : bliminf u f p = sSup { a | ∀ᶠ x in f, p x → a ≤ u x } :=
  rfl
/-
**Filter.liminf_comp** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：liminf_comp (u : β -> α) (v : γ -> β) (f : Filter γ) : liminf (u ∘ v) f = 
liminf u (map v f)
参数：u : β -> α；v : γ -> β；f : Filter γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liminf_comp (u : β → α) (v : γ → β) (f : Filter γ) :
    liminf (u ∘ v) f = liminf u (map v f) := rfl
/-
**Filter.limsup_comp** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsup_comp (u : β -> α) (v : γ -> β) (f : Filter γ) : limsup (u ∘ v) f = 
limsup u (map v f)
参数：u : β -> α；v : γ -> β；f : Filter γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma limsup_comp (u : β → α) (v : γ → β) (f : Filter γ) :
    limsup (u ∘ v) f = limsup u (map v f) := rfl

end

@[simp]
/-
**Filter.blimsup_true** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_true (f : Filter β) (u : β -> α) : (blimsup u f fun _ => True) = l
imsup u f
参数：f : Filter β；u : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blimsup_true (f : Filter β) (u : β → α) : (blimsup u f fun _ => True) = limsup u f := by
  simp [blimsup_eq, limsup_eq]

@[simp]
/-
**Filter.bliminf_true** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_true (f : Filter β) (u : β -> α) : (bliminf u f fun _ => True) = l
iminf u f
参数：f : Filter β；u : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bliminf_true (f : Filter β) (u : β → α) : (bliminf u f fun _ => True) = liminf u f := by
  simp [bliminf_eq, liminf_eq]
/-
**Filter.blimsup_eq_limsup** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：blimsup_eq_limsup {f : Filter β} {u : β -> α} {p : β -> Prop} : blimsup u 
f p = limsup u (f ⊓ 𝓟 {x | p x})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma blimsup_eq_limsup {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x}) := by
  simp only [blimsup_eq, limsup_eq, eventually_inf_principal, mem_ofPred_eq]
/-
**Filter.bliminf_eq_liminf** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：bliminf_eq_liminf {f : Filter β} {u : β -> α} {p : β -> Prop} : bliminf u 
f p = liminf u (f ⊓ 𝓟 {x | p x})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.blimsup_eq_limsup`：blimsup_eq_limsup {f : Filter β} {u : β -> α} 
{p : β -> Prop} : blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x})
-/
lemma bliminf_eq_liminf {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf u (f ⊓ 𝓟 {x | p x}) :=
  blimsup_eq_limsup (α := αᵒᵈ)
/-
**Filter.blimsup_eq_limsup_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_eq_limsup_subtype {f : Filter β} {u : β -> α} {p : β -> Prop} : bl
imsup u f p = limsup (u ∘ ((↑) : { x | p x } -> β)) (comap (↑) f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.blimsup_eq_limsup`：blimsup_eq_limsup {f : Filter β} {u : β -> α} 
{p : β -> Prop} : blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x})
· 使用定理 `Filter.limsup.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditionall
yCompleteLattice α] (u : β → α) (f : Filter β),   Filter.limsup u f = (Filter.ma
p u f).l…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_comap_setCoe_val`：map_comap_setCoe_val (f : Filter β) (s : Se
t β) : (f.comap ((↑) : s -> β)).map (↑) = f ⊓ 𝓟 s
-/
theorem blimsup_eq_limsup_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup (u ∘ ((↑) : { x | p x } → β)) (comap (↑) f) := by
  rw [blimsup_eq_limsup, limsup, limsup, ← map_map, map_comap_setCoe_val]
/-
**Filter.bliminf_eq_liminf_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_eq_liminf_subtype {f : Filter β} {u : β -> α} {p : β -> Prop} : bl
iminf u f p = liminf (u ∘ ((↑) : { x | p x } -> β)) (comap (↑) f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_eq_limsup_subtype`：blimsup_eq_limsup_subtype {f : Filter 
β} {u : β -> α} {p : β -> Prop} : blimsup u f p = limsup (u ∘ ((↑) : { x | p x }
 -> β)) (comap (↑) f)
-/
theorem bliminf_eq_liminf_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf (u ∘ ((↑) : { x | p x } → β)) (comap (↑) f) :=
  blimsup_eq_limsup_subtype (α := αᵒᵈ)
/-
**Filter.limsSup_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsSup_le_of_le {f : Filter α} {a} (hf : f.IsCobounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
-/
theorem limsSup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ᶠ n in f, n ≤ a) : limsSup f ≤ a :=
  csInf_le hf h
/-
**Filter.le_limsInf_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_limsInf_of_le {f : Filter α} {a} (hf : f.IsCobounded (· >= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem le_limsInf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ n) : a ≤ limsInf f :=
  le_csSup hf h
/-
**Filter.limsup_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_le_of_le {f : Filter β} {u : β -> α} {a} (hf : f.IsCoboundedUnder (
· <= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
-/
theorem limsup_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, u n ≤ a) : limsup u f ≤ a :=
  csInf_le hf h
/-
**Filter.le_liminf_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_liminf_of_le {f : Filter β} {u : β -> α} {a} (hf : f.IsCoboundedUnder (
· >= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f :=
  le_csSup hf h
/-
**Filter.le_limsSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_limsSup_of_le {f : Filter α} {a} (hf : f.IsBounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem le_limsSup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) : a ≤ limsSup f :=
  le_csInf hf h
/-
**Filter.limsInf_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_le_of_le {f : Filter α} {a} (hf : f.IsBounded (· >= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
-/
theorem limsInf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) : limsInf f ≤ a :=
  csSup_le hf h
/-
**Filter.le_limsup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_limsup_of_le {f : Filter β} {u : β -> α} {a} (hf : f.IsBoundedUnder (· 
<= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem le_limsup_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, u n ≤ b) → a ≤ b) : a ≤ limsup u f :=
  le_csInf hf h
/-
**Filter.liminf_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_of_le {f : Filter β} {u : β -> α} {a} (hf : f.IsBoundedUnder (· 
>= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
-/
theorem liminf_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ b, (∀ᶠ n in f, b ≤ u n) → b ≤ a) : liminf u f ≤ a :=
  csSup_le hf h
/-
**Filter.limsInf_le_limsSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_le_limsSup {f : Filter α} [NeBot f] (h₁ : f.IsBounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_of_le`：liminf_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· >= ·) u
· 使用定理 `Filter.le_limsup_of_le`：le_limsup_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem limsInf_le_limsSup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h₂ : f.IsBounded (· ≥ ·) := by isBoundedDefault) :
    limsInf f ≤ limsSup f :=
  liminf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsup_of_le h₁ fun a₁ ha₁ =>
      show a₀ ≤ a₁ from
        let ⟨_, hb₀, hb₁⟩ := (ha₀.and ha₁).exists
        le_trans hb₀ hb₁
/-
**Filter.liminf_le_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_limsup {f : Filter β} [NeBot f] {u : β -> α} (h : f.IsBoundedUnd
er (· <= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsInf_le_limsSup`：limsInf_le_limsSup {f : Filter α} [NeBot f] (
h₁ : f.IsBounded (· <= ·)
-/
theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α}
    (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ limsup u f :=
  limsInf_le_limsSup h h'
/-
**Filter.limsSup_le_limsSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsSup_le_limsSup {f g : Filter α} (hf : f.IsCobounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
-/
theorem limsSup_le_limsSup {f g : Filter α}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hg : g.IsBounded (· ≤ ·) := by isBoundedDefault)
    (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : limsSup f ≤ limsSup g :=
  csInf_le_csInf hf hg h
/-
**Filter.limsInf_le_limsInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_le_limsInf {f g : Filter α} (hf : f.IsBounded (· >= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le_csSup`：csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : 
s subseteq t) : sSup s <= sSup t
-/
theorem limsInf_le_limsInf {f g : Filter α}
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : limsInf f ≤ limsInf g :=
  csSup_le_csSup hg hf h
/-
**Filter.limsup_le_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_le_limsup {α : Type*} [ConditionallyCompleteLattice β] {f : Filter 
α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCoboundedUnder (· <= ·) u
参数：h : u <=ᶠ[f] v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsSup_le_limsSup`：limsSup_le_limsSup {f g : Filter α} (hf : f.I
sCobounded (· <= ·)
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
-/
theorem limsup_le_limsup {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : u ≤ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hv : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) :
    limsup u f ≤ limsup v f :=
  limsSup_le_limsSup hu hv fun _ => h.trans
/-
**Filter.liminf_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_liminf {α : Type*} [ConditionallyCompleteLattice β] {f : Filter 
α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (hu : f.IsBoundedUnder (· >= 
·) u
参数：h : forallᶠ a in f, u a <= v a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
-/
theorem liminf_le_liminf {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a ≤ v a)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hv : f.IsCoboundedUnder (· ≥ ·) v := by isBoundedDefault) :
    liminf u f ≤ liminf v f :=
  limsup_le_limsup (β := βᵒᵈ) h hv hu
/-
**Filter.limsSup_le_limsSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsSup_le_limsSup_of_le {f g : Filter α} (h : f <= g) (hf : f.IsCobounded
 (· <= ·)
参数：h : f <= g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsSup_le_limsSup`：limsSup_le_limsSup {f g : Filter α} (hf : f.I
sCobounded (· <= ·)
-/
theorem limsSup_le_limsSup_of_le {f g : Filter α} (h : f ≤ g)
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (hg : g.IsBounded (· ≤ ·) := by isBoundedDefault) :
    limsSup f ≤ limsSup g :=
  limsSup_le_limsSup hf hg fun _ ha => h ha
/-
**Filter.limsInf_le_limsInf_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_le_limsInf_of_le {f g : Filter α} (h : g <= f) (hf : f.IsBounded (
· >= ·)
参数：h : g <= f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsInf_le_limsInf`：limsInf_le_limsInf {f g : Filter α} (hf : f.I
sBounded (· >= ·)
-/
theorem limsInf_le_limsInf_of_le {f g : Filter α} (h : g ≤ f)
    (hf : f.IsBounded (· ≥ ·) := by isBoundedDefault)
    (hg : g.IsCobounded (· ≥ ·) := by isBoundedDefault) :
    limsInf f ≤ limsInf g :=
  limsInf_le_limsInf hf hg fun _ ha => h ha
/-
**Filter.limsup_le_limsup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filte
r α} (h : f <= g) {u : α -> β} (hf : f.IsCoboundedUnder (· <= ·) u
参数：h : f <= g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsSup_le_limsSup_of_le`：limsSup_le_limsSup_of_le {f g : Filter 
α} (h : f <= g) (hf : f.IsCobounded (· <= ·)
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f ≤ g)
    {u : α → β}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    limsup u f ≤ limsup u g :=
  limsSup_le_limsSup_of_le (map_mono h) hf hg
/-
**Filter.Tendsto.limsup_comp_le_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {ι : Type u_6} {α : Type u_7} {β : Type u_8} [inst : ConditionallyComple
teLattice β] {v : ι → α} {u : α → β}   {f : Filter ι} {g : Filter α},   Filter.T
endsto v f g →     autoParam (Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) (Fi
lter.map v f) u)         Filter.Tendsto.limsup_comp_le_limsup._auto_1 →       au
toParam (Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) g u) Filter.Tendsto.limsup
_comp_le_limsup._auto_3 →         Filter.limsup (u ∘ v) f ≤ Filter.limsup u g
参数：Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) (Filter.map v f) u；Filter.IsBo
undedUnder (fun x1 x2 => x1 ≤ x2) g u；u ∘ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.limsup_comp`：limsup_comp (u : β -> α) (v : γ -> β) (f : Filter γ)
 : limsup (u ∘ v) f = limsup u (map v f)
· 使用定理 `Filter.limsup_le_limsup_of_le`：limsup_le_limsup_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : f <= g) {u : α -> β} (hf : f.IsCoboun
dedUnder (· <= ·) u
-/
theorem Tendsto.limsup_comp_le_limsup {ι α β} [ConditionallyCompleteLattice β] {v : ι → α}
    {u : α → β} {f : Filter ι} {g : Filter α} (hv : Tendsto v f g)
    (hvf : (map v f).IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    limsup (u ∘ v) f ≤ limsup u g := by
  rw [limsup_comp]
  exact limsup_le_limsup_of_le hv
/-
**Filter.liminf_le_liminf_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filte
r α} (h : g <= f) {u : α -> β} (hf : f.IsBoundedUnder (· >= ·) u
参数：h : g <= f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsInf_le_limsInf_of_le`：limsInf_le_limsInf_of_le {f g : Filter 
α} (h : g <= f) (hf : f.IsBounded (· >= ·)
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g ≤ f)
    {u : α → β}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hg : g.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ liminf u g :=
  limsInf_le_limsInf_of_le (map_mono h) hf hg
/-
**Filter.Tendsto.liminf_le_liminf_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {ι : Type u_6} {α : Type u_7} {β : Type u_8} [inst : ConditionallyComple
teLattice β] {v : ι → α} {u : α → β}   {f : Filter ι} {g : Filter α},   Filter.T
endsto v f g →     autoParam (Filter.IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) (Fi
lter.map v f) u)         Filter.Tendsto.liminf_le_liminf_comp._auto_1 →       au
toParam (Filter.IsBoundedUnder (fun x1 x2 => x1 ≥ x2) g u) Filter.Tendsto.liminf
_le_liminf_comp._auto_3 →         Filter.liminf u g ≤ Filter.liminf (u ∘ v) f
参数：Filter.IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) (Filter.map v f) u；Filter.IsBo
undedUnder (fun x1 x2 => x1 ≥ x2) g u；u ∘ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.limsup_comp_le_limsup`：∀ {ι : Type u_6} {α : Type u_7} {β
 : Type u_8} [inst : ConditionallyCompleteLattice β] {v : ι → α} {u : α → β}   {
f : Filter ι} {g : Filter …
-/
theorem Tendsto.liminf_le_liminf_comp {ι α β} [ConditionallyCompleteLattice β] {v : ι → α}
    {u : α → β} {f : Filter ι} {g : Filter α} (hv : Tendsto v f g)
    (hvf : (map v f).IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hg : g.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u g ≤ liminf (u ∘ v) f :=
  hv.limsup_comp_le_limsup (β := βᵒᵈ)
/-
**Filter.limsSup_principal_eq_csSup** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsSup_principal_eq_csSup (h : BddAbove s) (hs : s.Nonempty) : limsSup (𝓟
 s) = sSup s
参数：h : BddAbove s；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `csInf_upperBounds_eq_csSup`：∀ {α : Type u_1} [inst : ConditionallyComple
teLattice α] {s : Set α},   BddAbove s → s.Nonempty → sInf (upperBounds s) = sSu
p s
-/
lemma limsSup_principal_eq_csSup (h : BddAbove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s := by
  simp only [limsSup, eventually_principal]; exact csInf_upperBounds_eq_csSup h hs
/-
**Filter.limsInf_principal_eq_csSup** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsInf_principal_eq_csSup (h : BddBelow s) (hs : s.Nonempty) : limsInf (𝓟
 s) = sInf s
参数：h : BddBelow s；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.limsSup_principal_eq_csSup`：limsSup_principal_eq_csSup (h : BddAb
ove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s
-/
lemma limsInf_principal_eq_csSup (h : BddBelow s) (hs : s.Nonempty) : limsInf (𝓟 s) = sInf s :=
  limsSup_principal_eq_csSup (α := αᵒᵈ) h hs
/-
**Filter.limsup_top_eq_ciSup** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsup_top_eq_ciSup [Nonempty β] (hu : BddAbove (range u)) : limsup u ⊤ = 
⨆ i, u i
参数：hu : BddAbove (range u)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditionall
yCompleteLattice α] (u : β → α) (f : Filter β),   Filter.limsup u f = (Filter.ma
p u f).l…
· 使用定理 `Filter.map_top`：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
· 使用引理 `Filter.limsSup_principal_eq_csSup`：limsSup_principal_eq_csSup (h : BddAb
ove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
-/
lemma limsup_top_eq_ciSup [Nonempty β] (hu : BddAbove (range u)) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup, map_top, limsSup_principal_eq_csSup hu (range_nonempty _), sSup_range]
/-
**Filter.liminf_top_eq_ciInf** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：liminf_top_eq_ciInf [Nonempty β] (hu : BddBelow (range u)) : liminf u ⊤ = 
⨅ i, u i
参数：hu : BddBelow (range u)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.liminf.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditionall
yCompleteLattice α] (u : β → α) (f : Filter β),   Filter.liminf u f = (Filter.ma
p u f).l…
· 使用定理 `Filter.map_top`：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
· 使用引理 `Filter.limsInf_principal_eq_csSup`：limsInf_principal_eq_csSup (h : BddBe
low s) (hs : s.Nonempty) : limsInf (𝓟 s) = sInf s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
-/
lemma liminf_top_eq_ciInf [Nonempty β] (hu : BddBelow (range u)) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf, map_top, limsInf_principal_eq_csSup hu (range_nonempty _), sInf_range]
/-
**Filter.limsup_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {
u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u f = limsup v f
参数：h : forallᶠ a in f, u a = v a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_eq`：limsup_eq : limsup u f = sInf { a | forallᶠ n in f, u 
n <= a }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem limsup_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : limsup u f = limsup v f := by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])
/-
**Filter.blimsup_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_congr {f : Filter β} {u v : β -> α} {p : β -> Prop} (h : forallᶠ a
 in f, p a -> u a = v a) : blimsup u f p = blimsup v f p
参数：h : forallᶠ a in f, p a -> u a = v a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.blimsup_eq_limsup`：blimsup_eq_limsup {f : Filter β} {u : β -> α} 
{p : β -> Prop} : blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x})
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
-/
theorem blimsup_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    blimsup u f p = blimsup v f p := by
  simpa only [blimsup_eq_limsup] using! limsup_congr <| eventually_inf_principal.2 h
/-
**Filter.bliminf_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_congr {f : Filter β} {u v : β -> α} {p : β -> Prop} (h : forallᶠ a
 in f, p a -> u a = v a) : bliminf u f p = bliminf v f p
参数：h : forallᶠ a in f, p a -> u a = v a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_congr`：blimsup_congr {f : Filter β} {u v : β -> α} {p : β
 -> Prop} (h : forallᶠ a in f, p a -> u a = v a) : blimsup u f p = blimsup v f p
-/
theorem bliminf_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    bliminf u f p = bliminf v f p :=
  blimsup_congr (α := αᵒᵈ) h
/-
**Filter.liminf_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {
u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u f = liminf v f
参数：h : forallᶠ a in f, u a = v a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
-/
theorem liminf_congr {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : liminf u f = liminf v f :=
  limsup_congr (β := βᵒᵈ) h

@[simp]
/-
**Filter.limsup_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [
NeBot f] (b : β) : limsup (fun _ => b) f = b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `csInf_Ici`：csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a : α} : sInf (Ici a) = a
-/
theorem limsup_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : limsup (fun _ => b) f = b := by
  simpa only [limsup_eq, eventually_const] using! csInf_Ici

@[simp]
/-
**Filter.liminf_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [
NeBot f] (b : β) : liminf (fun _ => b) f = b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
-/
theorem liminf_const {α : Type*} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : liminf (fun _ => b) f = b :=
  limsup_const (β := βᵒᵈ) b
/-
**Filter.HasBasis.liminf_eq_sSup_iUnion_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.HasBasis`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {ι : Type u_6} {ι
' : Type u_7} {f : ι → α} {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι}, v.H
asBasis p s → Filter.liminf f v = sSup (⋃ j, ⋂ i, Set.Iic (f ↑i))
参数：⋃ j, ⋂ i, Set.Iic (f ↑i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.liminf_eq_sSup_iUnion_iInter {ι ι' : Type*} {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) :
    liminf f v = sSup (⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i)) := by
  simp_rw [liminf_eq, hv.eventually_iff]
  congr 1
  ext x
  simp only [mem_ofPred_eq, iInter_coe_set, mem_iUnion, mem_iInter, mem_Iic, Subtype.exists,
    exists_prop]
/-
**Filter.HasBasis.liminf_eq_sSup_univ_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : ConditionallyCompl
eteLattice α] {f : ι → α} {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι}, v.H
asBasis p s → ∀ (i : ι'), p i → s i = ∅ → Filter.liminf f v = sSup Set.univ
参数：i : ι'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.eq_bot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l = ⊥ ↔ ∃ i, p i ∧ s i = 
∅)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasBasis.liminf_eq_sSup_univ_of_empty {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) (i : ι') (hi : p i) (h'i : s i = ∅) :
    liminf f v = sSup univ := by
  simp [hv.eq_bot_iff.2 ⟨i, hi, h'i⟩, liminf_eq]
/-
**Filter.HasBasis.limsup_eq_sInf_iUnion_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.HasBasis`。
形式化陈述：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {ι : Type u_6} {ι
' : Type u_7} {f : ι → α} {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι}, v.H
asBasis p s → Filter.limsup f v = sInf (⋃ j, ⋂ i, Set.Ici (f ↑i))
参数：⋃ j, ⋂ i, Set.Ici (f ↑i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.liminf_eq_sSup_iUnion_iInter`：∀ {α : Type u_1} [inst : C
onditionallyCompleteLattice α] {ι : Type u_6} {ι' : Type u_7} {f : ι → α} {v : F
ilter ι}   {p : ι' → Prop} {s : ι'…
-/
theorem HasBasis.limsup_eq_sInf_iUnion_iInter {ι ι' : Type*} {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) :
    limsup f v = sInf (⋃ (j : Subtype p), ⋂ (i : s j), Ici (f i)) :=
  HasBasis.liminf_eq_sSup_iUnion_iInter (α := αᵒᵈ) hv
/-
**Filter.HasBasis.limsup_eq_sInf_univ_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : ConditionallyCompl
eteLattice α] {f : ι → α} {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι}, v.H
asBasis p s → ∀ (i : ι'), p i → s i = ∅ → Filter.limsup f v = sInf Set.univ
参数：i : ι'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.liminf_eq_sSup_univ_of_empty`：∀ {α : Type u_1} {ι : Type
 u_4} {ι' : Type u_5} [inst : ConditionallyCompleteLattice α] {f : ι → α} {v : F
ilter ι}   {p : ι' → Prop} {s : ι'…
-/
theorem HasBasis.limsup_eq_sInf_univ_of_empty {f : ι → α} {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} (hv : v.HasBasis p s) (i : ι') (hi : p i) (h'i : s i = ∅) :
    limsup f v = sInf univ :=
  HasBasis.liminf_eq_sSup_univ_of_empty (α := αᵒᵈ) hv i hi h'i

@[simp]
/-
**Filter.liminf_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_nat_add (f : Nat -> α) (k : Nat) : liminf (fun i => f (i + k)) atTo
p = liminf f atTop
参数：f : Nat -> α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Filter.liminf.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditionall
yCompleteLattice α] (u : β → α) (f : Filter β),   Filter.liminf u f = (Filter.ma
p u f).l…
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_add_atTop_eq_nat`：map_add_atTop_eq_nat (k : Nat) : map (fun a
 => a + k) atTop = atTop
-/
theorem liminf_nat_add (f : ℕ → α) (k : ℕ) :
    liminf (fun i => f (i + k)) atTop = liminf f atTop := by
  rw [← Function.comp_def, liminf, liminf, ← map_map, map_add_atTop_eq_nat]

@[simp]
/-
**Filter.limsup_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_nat_add (f : Nat -> α) (k : Nat) : limsup (fun i => f (i + k)) atTo
p = limsup f atTop
参数：f : Nat -> α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_nat_add`：liminf_nat_add (f : Nat -> α) (k : Nat) : liminf 
(fun i => f (i + k)) atTop = liminf f atTop
-/
theorem limsup_nat_add (f : ℕ → α) (k : ℕ) : limsup (fun i => f (i + k)) atTop = limsup f atTop :=
  @liminf_nat_add αᵒᵈ _ f k

variable {f : Filter ι} {u : ι → α} {a : α}
/-
**Filter.le_limsup_of_frequently_le** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：le_limsup_of_frequently_le (hu : existsᶠ i in f, a <= u i) (hu_le : f.IsBo
undedUnder (· <= ·) u
参数：hu : existsᶠ i in f, a <= u i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_limsup_of_le`：le_limsup_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma le_limsup_of_frequently_le (hu : ∃ᶠ i in f, a ≤ u i)
    (hu_le : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) : a ≤ limsup u f := by
  refine le_limsup_of_le hu_le fun b hb ↦ ?_
  obtain ⟨n, han, hnb⟩ := (hu.and_eventually hb).exists
  exact han.trans hnb
/-
**Filter.liminf_le_of_frequently_le** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：liminf_le_of_frequently_le (hu : existsᶠ i in f, u i <= a) (hu_le : f.IsBo
undedUnder (· >= ·) u
参数：hu : existsᶠ i in f, u i <= a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_of_le`：liminf_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· >= ·) u
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma liminf_le_of_frequently_le (hu : ∃ᶠ i in f, u i ≤ a)
    (hu_le : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : liminf u f ≤ a := by
  refine liminf_le_of_le hu_le fun b hb ↦ ?_
  obtain ⟨n, hna, hbn⟩ := (hu.and_eventually hb).exists
  exact hbn.trans hna

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

@[simp]
/-
**Filter.limsSup_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsSup_bot : limsSup (⊥ : Filter α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem limsSup_bot : limsSup (⊥ : Filter α) = ⊥ :=
  bot_unique <| sInf_le <| by simp
/-
**Filter.limsup_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] (f : β → α), Fi
lter.limsup f ⊥ = ⊥
参数：f : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `Filter.limsSup_bot`：limsSup_bot : limsSup (⊥ : Filter α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem limsup_bot (f : β → α) : limsup f ⊥ = ⊥ := by simp [limsup]

@[simp]
/-
**Filter.limsInf_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_bot : limsInf (⊥ : Filter α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem limsInf_bot : limsInf (⊥ : Filter α) = ⊤ :=
  top_unique <| le_sSup <| by simp
/-
**Filter.liminf_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] (f : β → α), Fi
lter.liminf f ⊥ = ⊤
参数：f : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `Filter.limsInf_bot`：limsInf_bot : limsInf (⊥ : Filter α) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem liminf_bot (f : β → α) : liminf f ⊥ = ⊤ := by simp [liminf]

@[simp]
/-
**Filter.limsSup_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsSup_top : limsSup (⊤ : Filter α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem limsSup_top : limsSup (⊤ : Filter α) = ⊤ :=
  top_unique <| le_sInf <| by simpa [eq_univ_iff_forall] using fun b hb => top_unique <| hb _

@[simp]
/-
**Filter.limsInf_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_top : limsInf (⊤ : Filter α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem limsInf_top : limsInf (⊤ : Filter α) = ⊥ :=
  bot_unique <| sSup_le <| by simpa [eq_univ_iff_forall] using fun b hb => bot_unique <| hb _

@[simp]
/-
**Filter.blimsup_false** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_false {f : Filter β} {u : β -> α} : (blimsup u f fun _ => False) =
 ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `sInf_univ`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf Set.univ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blimsup_false {f : Filter β} {u : β → α} : (blimsup u f fun _ => False) = ⊥ := by
  simp [blimsup_eq]

@[simp]
/-
**Filter.bliminf_false** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_false {f : Filter β} {u : β -> α} : (bliminf u f fun _ => False) =
 ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `sSup_univ`：sSup_univ : sSup univ = (⊤ : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bliminf_false {f : Filter β} {u : β → α} : (bliminf u f fun _ => False) = ⊤ := by
  simp [bliminf_eq]

/-- Same as `limsup_const` applied to `⊥` but without the `NeBot f` assumption -/
@[simp]
/-
**Filter.limsup_const_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_const_bot {f : Filter β} : limsup (fun _ : β => (⊥ : α)) f = (⊥ : α
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_eq`：limsup_eq : limsup u f = sInf { a | forallᶠ n in f, u 
n <= a }
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Same as `limsup_const` applied to `⊥` but without the `NeBot f` assumption
-/
theorem limsup_const_bot {f : Filter β} : limsup (fun _ : β => (⊥ : α)) f = (⊥ : α) := by
  rw [limsup_eq, eq_bot_iff]
  exact sInf_le (Eventually.of_forall fun _ => le_rfl)

/-- Same as `limsup_const` applied to `⊤` but without the `NeBot f` assumption -/
@[simp]
/-
**Filter.liminf_const_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_const_top {f : Filter β} : liminf (fun _ : β => (⊤ : α)) f = (⊤ : α
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_const_bot`：limsup_const_bot {f : Filter β} : limsup (fun _
 : β => (⊥ : α)) f = (⊥ : α)

--- 原说明 ---
Same as `limsup_const` applied to `⊤` but without the `NeBot f` assumption
-/
theorem liminf_const_top {f : Filter β} : liminf (fun _ : β => (⊤ : α)) f = (⊤ : α) :=
  limsup_const_bot (α := αᵒᵈ)
/-
**Filter.HasBasis.limsSup_eq_iInf_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Sort u_6} {p : ι → Prop} 
{s : ι → Set α} {f : Filter α},   f.HasBasis p s → f.limsSup = ⨅ i, ⨅ (_ : p i),
 sSup (s i)
参数：_ : p i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
-/
theorem HasBasis.limsSup_eq_iInf_sSup {ι} {p : ι → Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    limsSup f = ⨅ (i) (_ : p i), sSup (s i) :=
  le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun _ => le_sSup⟩)
    (le_sInf fun _ ha =>
      let ⟨_, hi, ha⟩ := h.eventually_iff.1 ha
      iInf₂_le_of_le _ hi <| sSup_le ha)
/-
**Filter.HasBasis.limsInf_eq_iSup_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : CompleteLattice α] {p : ι → Prop} 
{s : ι → Set α} {f : Filter α},   f.HasBasis p s → f.limsInf = ⨆ i, ⨆ (_ : p i),
 sInf (s i)
参数：_ : p i；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.limsSup_eq_iInf_sSup`：∀ {α : Type u_1} [inst : CompleteL
attice α] {ι : Sort u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasB
asis p s → f.limsSup = ⨅ i…
-/
theorem HasBasis.limsInf_eq_iSup_sInf {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (h : f.HasBasis p s) : limsInf f = ⨆ (i) (_ : p i), sInf (s i) :=
  HasBasis.limsSup_eq_iInf_sSup (α := αᵒᵈ) h
/-
**Filter.limsSup_eq_iInf_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsSup_eq_iInf_sSup {f : Filter α} : limsSup f = ⨅ s in f, sSup s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.limsSup_eq_iInf_sSup`：∀ {α : Type u_1} [inst : CompleteL
attice α] {ι : Sort u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasB
asis p s → f.limsSup = ⨅ i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem limsSup_eq_iInf_sSup {f : Filter α} : limsSup f = ⨅ s ∈ f, sSup s :=
  f.basis_sets.limsSup_eq_iInf_sSup
/-
**Filter.limsInf_eq_iSup_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsInf_eq_iSup_sInf {f : Filter α} : limsInf f = ⨆ s in f, sInf s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsSup_eq_iInf_sSup`：limsSup_eq_iInf_sSup {f : Filter α} : limsS
up f = ⨅ s in f, sSup s
-/
theorem limsInf_eq_iSup_sInf {f : Filter α} : limsInf f = ⨆ s ∈ f, sInf s :=
  limsSup_eq_iInf_sSup (α := αᵒᵈ)
/-
**Filter.limsup_le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_le_iSup {f : Filter β} {u : β -> α} : limsup u f <= ⨆ n, u n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem limsup_le_iSup {f : Filter β} {u : β → α} : limsup u f ≤ ⨆ n, u n :=
  limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall (le_iSup u))
/-
**Filter.iInf_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iInf_le_liminf {f : Filter β} {u : β -> α} : ⨅ n, u n <= liminf u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem iInf_le_liminf {f : Filter β} {u : β → α} : ⨅ n, u n ≤ liminf u f :=
  le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall (iInf_le u))

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
/-
**Filter.limsup_eq_iInf_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_eq_iInf_iSup {f : Filter β} {u : β -> α} : limsup u f = ⨅ s in f, ⨆
 a in s, u a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.limsSup_eq_iInf_sSup`：∀ {α : Type u_1} [inst : CompleteL
attice α] {ι : Sort u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasB
asis p s → f.limsSup = ⨅ i…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a complete lattice, the limsup of a function is the infimum over sets `s` in 
the filter
of the supremum of the function over `s`
-/
theorem limsup_eq_iInf_iSup {f : Filter β} {u : β → α} : limsup u f = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
  (f.basis_sets.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]
/-
**Filter.limsup_eq_iInf_iSup_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_eq_iInf_iSup_of_nat {u : Nat -> α} : limsup u atTop = ⨅ n : Nat, ⨆ 
i >= n, u i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.limsSup_eq_iInf_sSup`：∀ {α : Type u_1} [inst : CompleteL
attice α] {ι : Sort u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasB
asis p s → f.limsSup = ⨅ i…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `iInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
a : α} [Nonempty ι], ⨅ x, a = a
-/
theorem limsup_eq_iInf_iSup_of_nat {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
  (atTop_basis.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, iInf_const]; rfl
/-
**Filter.limsup_eq_iInf_iSup_of_nat'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_eq_iInf_iSup_of_nat' {u : Nat -> α} : limsup u atTop = ⨅ n : Nat, ⨆
 i : Nat, u (i + n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_eq_iInf_iSup_of_nat`：limsup_eq_iInf_iSup_of_nat {u : Nat -
> α} : limsup u atTop = ⨅ n : Nat, ⨆ i >= n, u i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_ge_eq_iSup_nat_add`：iSup_ge_eq_iSup_nat_add (u : Nat -> α) (n : Nat
) : ⨆ i >= n, u i = ⨆ i, u (i + n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limsup_eq_iInf_iSup_of_nat' {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) := by
  simp only [limsup_eq_iInf_iSup_of_nat, iSup_ge_eq_iSup_nat_add]
/-
**Filter.HasBasis.limsup_eq_iInf_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : CompleteLattice α] 
{p : ι → Prop} {s : ι → Set β} {f : Filter β}   {u : β → α}, f.HasBasis p s → Fi
lter.limsup u f = ⨅ i, ⨅ (_ : p i), ⨆ a ∈ s i, u a
参数：_ : p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.limsSup_eq_iInf_sSup`：∀ {α : Type u_1} [inst : CompleteL
attice α] {ι : Sort u_6} {p : ι → Prop} {s : ι → Set α} {f : Filter α},   f.HasB
asis p s → f.limsSup = ⨅ i…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasBasis.limsup_eq_iInf_iSup {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : limsup u f = ⨅ (i) (_ : p i), ⨆ a ∈ s i, u a :=
  (h.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image]
/-
**Filter.limsSup_principal_eq_sSup** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsSup_principal_eq_sSup (s : Set α) : limsSup (𝓟 s) = sSup s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sInf_upperBounds_eq_sSup`：∀ {α : Type u_1} [inst : CompleteLattice α] (s
 : Set α), sInf (upperBounds s) = sSup s
-/
lemma limsSup_principal_eq_sSup (s : Set α) : limsSup (𝓟 s) = sSup s := by
  simpa only [limsSup, eventually_principal] using! sInf_upperBounds_eq_sSup s
/-
**Filter.limsInf_principal_eq_sInf** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsInf_principal_eq_sInf (s : Set α) : limsInf (𝓟 s) = sInf s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `sSup_lowerBounds_eq_sInf`：sSup_lowerBounds_eq_sInf (s : Set α) : sSup (l
owerBounds s) = sInf s
-/
lemma limsInf_principal_eq_sInf (s : Set α) : limsInf (𝓟 s) = sInf s := by
  simpa only [limsInf, eventually_principal] using! sSup_lowerBounds_eq_sInf s
/-
**Filter.limsup_top_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] (u : β → α), Fi
lter.limsup u ⊤ = ⨆ i, u i
参数：u : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditionall
yCompleteLattice α] (u : β → α) (f : Filter β),   Filter.limsup u f = (Filter.ma
p u f).l…
· 使用定理 `Filter.map_top`：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
· 使用引理 `Filter.limsSup_principal_eq_sSup`：limsSup_principal_eq_sSup (s : Set α) 
: limsSup (𝓟 s) = sSup s
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
-/
@[simp] lemma limsup_top_eq_iSup (u : β → α) : limsup u ⊤ = ⨆ i, u i := by
  rw [limsup, map_top, limsSup_principal_eq_sSup, sSup_range]
/-
**Filter.liminf_top_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] (u : β → α), Fi
lter.liminf u ⊤ = ⨅ i, u i
参数：u : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.liminf.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditionall
yCompleteLattice α] (u : β → α) (f : Filter β),   Filter.liminf u f = (Filter.ma
p u f).l…
· 使用定理 `Filter.map_top`：map_top (f : α -> β) : map f ⊤ = 𝓟 (range f)
· 使用引理 `Filter.limsInf_principal_eq_sInf`：limsInf_principal_eq_sInf (s : Set α) 
: limsInf (𝓟 s) = sInf s
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
-/
@[simp] lemma liminf_top_eq_iInf (u : β → α) : liminf u ⊤ = ⨅ i, u i := by
  rw [liminf, map_top, limsInf_principal_eq_sInf, sInf_range]
/-
**Filter.blimsup_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_congr' {f : Filter β} {p q : β -> Prop} {u : β -> α} (h : forallᶠ 
x in f, u x != ⊥ -> (p x ↔ q x)) : blimsup u f p = blimsup u f q
参数：h : forallᶠ x in f, u x != ⊥ -> (p x ↔ q x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem blimsup_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊥ → (p x ↔ q x)) : blimsup u f p = blimsup u f q := by
  simp only [blimsup_eq]
  congr with a
  refine eventually_congr (h.mono fun b hb => ?_)
  rcases eq_or_ne (u b) ⊥ with hu | hu; · simp [hu]
  rw [hb hu]
/-
**Filter.bliminf_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_congr' {f : Filter β} {p q : β -> Prop} {u : β -> α} (h : forallᶠ 
x in f, u x != ⊤ -> (p x ↔ q x)) : bliminf u f p = bliminf u f q
参数：h : forallᶠ x in f, u x != ⊤ -> (p x ↔ q x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_congr'`：blimsup_congr' {f : Filter β} {p q : β -> Prop} {
u : β -> α} (h : forallᶠ x in f, u x != ⊥ -> (p x ↔ q x)) : blimsup u f p = blim
sup u f q
-/
theorem bliminf_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊤ → (p x ↔ q x)) : bliminf u f p = bliminf u f q :=
  blimsup_congr' (α := αᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.HasBasis.blimsup_eq_iInf_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : CompleteLattice α] 
{p : ι → Prop} {s : ι → Set β} {f : Filter β}   {u : β → α}, f.HasBasis p s → ∀ 
{q : β → Prop}, Filter.blimsup u f q = ⨅ i, ⨅ (_ : p i), ⨆ a ∈ s i, ⨆ (_ : q a),
 u a
参数：_ : p i；_ : q a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.blimsup_eq_limsup`：blimsup_eq_limsup {f : Filter β} {u : β -> α} 
{p : β -> Prop} : blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x})
· 使用定理 `Filter.HasBasis.limsup_eq_iInf_iSup`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_4} [inst : CompleteLattice α] {p : ι → Prop} {s : ι → Set β} {f : Filte
r β}   {u : β → α}, f.Has…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasBasis.blimsup_eq_iInf_iSup {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (hf : f.HasBasis p s) {q : β → Prop} :
    blimsup u f q = ⨅ (i) (_ : p i), ⨆ a ∈ s i, ⨆ (_ : q a), u a := by
  simp only [blimsup_eq_limsup, (hf.inf_principal _).limsup_eq_iInf_iSup, mem_inter_iff, iSup_and,
    mem_ofPred_eq]
/-
**Filter.blimsup_eq_iInf_biSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_eq_iInf_biSup {f : Filter β} {p : β -> Prop} {u : β -> α} : blimsu
p u f p = ⨅ s in f, ⨆ (b) (_ : p b ∧ b in s), u b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.blimsup_eq_iInf_iSup`：∀ {α : Type u_1} {β : Type u_2} {ι
 : Type u_4} [inst : CompleteLattice α] {p : ι → Prop} {s : ι → Set β} {f : Filt
er β}   {u : β → α}, f.Has…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_and'`：iSup_and' {p q : Prop} {s : p -> q -> α} : ⨆ (h₁ : p) (h₂ : q
), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blimsup_eq_iInf_biSup {f : Filter β} {p : β → Prop} {u : β → α} :
    blimsup u f p = ⨅ s ∈ f, ⨆ (b) (_ : p b ∧ b ∈ s), u b := by
  simp only [f.basis_sets.blimsup_eq_iInf_iSup, iSup_and', id, and_comm]
/-
**Filter.blimsup_eq_iInf_biSup_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_eq_iInf_biSup_of_nat {p : Nat -> Prop} {u : Nat -> α} : blimsup u 
atTop p = ⨅ i, ⨆ (j) (_ : p j ∧ i <= j), u j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.blimsup_eq_iInf_iSup`：∀ {α : Type u_1} {β : Type u_2} {ι
 : Type u_4} [inst : CompleteLattice α] {p : ι → Prop} {s : ι → Set β} {f : Filt
er β}   {u : β → α}, f.Has…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iInf_true`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : True → α}, i
Inf s = s trivial
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blimsup_eq_iInf_biSup_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    blimsup u atTop p = ⨅ i, ⨆ (j) (_ : p j ∧ i ≤ j), u j := by
  simp only [atTop_basis.blimsup_eq_iInf_iSup, @and_comm (p _), iSup_and, mem_Ici, iInf_true]

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
/-
**Filter.liminf_eq_iSup_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_eq_iSup_iInf {f : Filter β} {u : β -> α} : liminf u f = ⨆ s in f, ⨅
 a in s, u a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_eq_iInf_iSup`：limsup_eq_iInf_iSup {f : Filter β} {u : β ->
 α} : limsup u f = ⨅ s in f, ⨆ a in s, u a

--- 原说明 ---
In a complete lattice, the liminf of a function is the infimum over sets `s` in 
the filter
of the supremum of the function over `s`
-/
theorem liminf_eq_iSup_iInf {f : Filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
  limsup_eq_iInf_iSup (α := αᵒᵈ)
/-
**Filter.liminf_eq_iSup_iInf_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_eq_iSup_iInf_of_nat {u : Nat -> α} : liminf u atTop = ⨆ n : Nat, ⨅ 
i >= n, u i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_eq_iInf_iSup_of_nat`：limsup_eq_iInf_iSup_of_nat {u : Nat -
> α} : limsup u atTop = ⨅ n : Nat, ⨆ i >= n, u i
-/
theorem liminf_eq_iSup_iInf_of_nat {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
  @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u
/-
**Filter.liminf_eq_iSup_iInf_of_nat'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_eq_iSup_iInf_of_nat' {u : Nat -> α} : liminf u atTop = ⨆ n : Nat, ⨅
 i : Nat, u (i + n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_eq_iInf_iSup_of_nat'`：limsup_eq_iInf_iSup_of_nat' {u : Nat
 -> α} : limsup u atTop = ⨅ n : Nat, ⨆ i : Nat, u (i + n)
-/
theorem liminf_eq_iSup_iInf_of_nat' {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
  @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _
/-
**Filter.HasBasis.liminf_eq_iSup_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : CompleteLattice α] 
{p : ι → Prop} {s : ι → Set β} {f : Filter β}   {u : β → α}, f.HasBasis p s → Fi
lter.liminf u f = ⨆ i, ⨆ (_ : p i), ⨅ a ∈ s i, u a
参数：_ : p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.limsup_eq_iInf_iSup`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_4} [inst : CompleteLattice α] {p : ι → Prop} {s : ι → Set β} {f : Filte
r β}   {u : β → α}, f.Has…
-/
theorem HasBasis.liminf_eq_iSup_iInf {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : liminf u f = ⨆ (i) (_ : p i), ⨅ a ∈ s i, u a :=
  HasBasis.limsup_eq_iInf_iSup (α := αᵒᵈ) h
/-
**Filter.bliminf_eq_iSup_biInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_eq_iSup_biInf {f : Filter β} {p : β -> Prop} {u : β -> α} : blimin
f u f p = ⨆ s in f, ⨅ (b) (_ : p b ∧ b in s), u b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_eq_iInf_biSup`：blimsup_eq_iInf_biSup {f : Filter β} {p : 
β -> Prop} {u : β -> α} : blimsup u f p = ⨅ s in f, ⨆ (b) (_ : p b ∧ b in s), u 
b
-/
theorem bliminf_eq_iSup_biInf {f : Filter β} {p : β → Prop} {u : β → α} :
    bliminf u f p = ⨆ s ∈ f, ⨅ (b) (_ : p b ∧ b ∈ s), u b :=
  @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u
/-
**Filter.bliminf_eq_iSup_biInf_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_eq_iSup_biInf_of_nat {p : Nat -> Prop} {u : Nat -> α} : bliminf u 
atTop p = ⨆ i, ⨅ (j) (_ : p j ∧ i <= j), u j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_eq_iInf_biSup_of_nat`：blimsup_eq_iInf_biSup_of_nat {p : N
at -> Prop} {u : Nat -> α} : blimsup u atTop p = ⨅ i, ⨆ (j) (_ : p j ∧ i <= j), 
u j
-/
theorem bliminf_eq_iSup_biInf_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    bliminf u atTop p = ⨆ i, ⨅ (j) (_ : p j ∧ i ≤ j), u j :=
  @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u
/-
**Filter.iSup_liminf_le_liminf_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_liminf_le_liminf_iSup {f : Filter β} {u : ι -> β -> α} : ⨆ i, liminf 
(u i) f <= liminf (fun b => ⨆ i, u i b) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Filter.liminf_le_liminf`：liminf_le_liminf {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (h
u : f.IsBound…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem iSup_liminf_le_liminf_iSup {f : Filter β} {u : ι → β → α} :
    ⨆ i, liminf (u i) f ≤ liminf (fun b ↦ ⨆ i, u i b) f :=
  iSup_le fun i ↦ liminf_le_liminf <| .of_forall fun b ↦ le_iSup (u · b) i
/-
**Filter.limsup_iInf_le_iInf_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_iInf_le_iInf_limsup {f : Filter β} {u : ι -> β -> α} : limsup (fun 
b => ⨅ i, u i b) f <= ⨅ i, limsup (u i) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.iSup_liminf_le_liminf_iSup`：iSup_liminf_le_liminf_iSup {f : Filte
r β} {u : ι -> β -> α} : ⨆ i, liminf (u i) f <= liminf (fun b => ⨆ i, u i b) f
-/
theorem limsup_iInf_le_iInf_limsup {f : Filter β} {u : ι → β → α} :
    limsup (fun b ↦ ⨅ i, u i b) f ≤ ⨅ i, limsup (u i) f :=
  iSup_liminf_le_liminf_iSup (α := αᵒᵈ)
/-
**Filter.limsup_eq_sInf_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_eq_sInf_sSup {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : 
ι -> R) : limsup a F = sInf ((fun I => sSup (a '' I)) '' F.sets)
参数：F : Filter ι；a : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_eq`：limsup_eq : limsup u f = sInf { a | forallᶠ n in f, u 
n <= a }
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `sInf_le_of_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : S
et α} {a b : α}, b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
-/
theorem limsup_eq_sInf_sSup {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    limsup a F = sInf ((fun I => sSup (a '' I)) '' F.sets) := by
  apply le_antisymm
  · rw [limsup_eq]
    refine sInf_le_sInf fun x hx => ?_
    rcases (mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F] with i hi
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
  · refine le_sInf fun b hb => sInf_le_of_le (mem_image_of_mem _ hb) <| sSup_le ?_
    rintro _ ⟨_, h, rfl⟩
    exact h
/-
**Filter.liminf_eq_sSup_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_eq_sSup_sInf {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : 
ι -> R) : liminf a F = sSup ((fun I => sInf (a '' I)) '' F.sets)
参数：F : Filter ι；a : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_eq_sInf_sSup`：limsup_eq_sInf_sSup {ι R : Type*} (F : Filte
r ι) [CompleteLattice R] (a : ι -> R) : limsup a F = sInf ((fun I => sSup (a '' 
I)) '' F.sets)
-/
theorem liminf_eq_sSup_sInf {ι R : Type*} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    liminf a F = sSup ((fun I => sInf (a '' I)) '' F.sets) :=
  @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a
/-
**Filter.liminf_le_of_frequently_le'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : 
α -> β} {x : β} (h : existsᶠ a in f, u a <= x) : liminf u f <= x
参数：h : existsᶠ a in f, u a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.liminf_eq`：liminf_eq : liminf u f = sSup { a | forallᶠ n in f, a 
<= u n }
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
-/
theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, u a ≤ x) : liminf u f ≤ x := by
  rw [liminf_eq]
  refine sSup_le fun b hb => ?_
  have hbx : ∃ᶠ _ in f, b ≤ x := by
    contrapose! h
    exact hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.choose_spec
/-
**Filter.le_limsup_of_frequently_le'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : 
α -> β} {x : β} (h : existsᶠ a in f, x <= u a) : x <= limsup u f
参数：h : existsᶠ a in f, x <= u a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_of_frequently_le'`：liminf_le_of_frequently_le' {α β} [C
ompleteLattice β] {f : Filter α} {u : α -> β} {x : β} (h : existsᶠ a in f, u a <
= x) : liminf u f <= x
-/
theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, x ≤ u a) : x ≤ limsup u f :=
  liminf_le_of_frequently_le' (β := βᵒᵈ) h

/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp]
/-
**Filter._root_.CompleteLatticeHom.apply_limsup_iterate** 是 Mathlib 中的一个定理，位于命名空
间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → α` is a morphism of complete lattices, then the limsup of its iterat
es of any
`a : α` is a fixed point.
-/
theorem _root_.CompleteLatticeHom.apply_limsup_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (limsup (fun n => f^[n] a) atTop) = limsup (fun n => f^[n] a) atTop := by
  rw [limsup_eq_iInf_iSup_of_nat', map_iInf]
  simp_rw [_root_.map_iSup, ← Function.comp_apply (f := f), ← Function.iterate_succ' f,
    ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ (0 < ·)]
  simp only [not_lt, Nat.le_zero, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  refine (iInf_le (fun i => ⨆ j, f^[j + (i + 1)] a) 0).trans ?_
  simp only [zero_add, iSup_le_iff]
  exact fun i => le_iSup (fun i => f^[i] a) (i + 1)

/-- If `f : α → α` is a morphism of complete lattices, then the liminf of its iterates of any
`a : α` is a fixed point. -/
/-
**Filter._root_.CompleteLatticeHom.apply_liminf_iterate** 是 Mathlib 中的一个定理，位于命名空
间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → α` is a morphism of complete lattices, then the liminf of its iterat
es of any
`a : α` is a fixed point.
-/
theorem _root_.CompleteLatticeHom.apply_liminf_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (liminf (fun n => f^[n] a) atTop) = liminf (fun n => f^[n] a) atTop :=
  (CompleteLatticeHom.dual f).apply_limsup_iterate _

variable {f g : Filter β} {p q : β → Prop} {u v : β → α}
/-
**Filter.blimsup_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_mono (h : forall x, p x -> q x) : blimsup u f p <= blimsup u f q
参数：h : forall x, p x -> q x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
theorem blimsup_mono (h : ∀ x, p x → q x) : blimsup u f p ≤ blimsup u f q :=
  sInf_le_sInf fun a ha => ha.mono <| by tauto
/-
**Filter.bliminf_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_antitone (h : forall x, p x -> q x) : bliminf u f q <= bliminf u f
 p
参数：h : forall x, p x -> q x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
theorem bliminf_antitone (h : ∀ x, p x → q x) : bliminf u f q ≤ bliminf u f p :=
  sSup_le_sSup fun a ha => ha.mono <| by tauto
/-
**Filter.mono_blimsup'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mono_blimsup' (h : forallᶠ x in f, p x -> u x <= v x) : blimsup u f p <= b
limsup v f p
参数：h : forallᶠ x in f, p x -> u x <= v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mono_blimsup' (h : ∀ᶠ x in f, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  sInf_le_sInf fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.2 hx').trans (hx.1 hx')
/-
**Filter.mono_blimsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mono_blimsup (h : forall x, p x -> u x <= v x) : blimsup u f p <= blimsup 
v f p
参数：h : forall x, p x -> u x <= v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mono_blimsup'`：mono_blimsup' (h : forallᶠ x in f, p x -> u x <= v
 x) : blimsup u f p <= blimsup v f p
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem mono_blimsup (h : ∀ x, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  mono_blimsup' <| Eventually.of_forall h
/-
**Filter.mono_bliminf'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mono_bliminf' (h : forallᶠ x in f, p x -> u x <= v x) : bliminf u f p <= b
liminf v f p
参数：h : forallᶠ x in f, p x -> u x <= v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mono_bliminf' (h : ∀ᶠ x in f, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  sSup_le_sSup fun _ ha => (ha.and h).mono fun _ hx hx' => (hx.1 hx').trans (hx.2 hx')
/-
**Filter.mono_bliminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mono_bliminf (h : forall x, p x -> u x <= v x) : bliminf u f p <= bliminf 
v f p
参数：h : forall x, p x -> u x <= v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mono_bliminf'`：mono_bliminf' (h : forallᶠ x in f, p x -> u x <= v
 x) : bliminf u f p <= bliminf v f p
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem mono_bliminf (h : ∀ x, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  mono_bliminf' <| Eventually.of_forall h
/-
**Filter.bliminf_antitone_filter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_antitone_filter (h : f <= g) : bliminf u g p <= bliminf u f p
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
-/
theorem bliminf_antitone_filter (h : f ≤ g) : bliminf u g p ≤ bliminf u f p :=
  sSup_le_sSup fun _ ha => ha.filter_mono h
/-
**Filter.blimsup_monotone_filter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_monotone_filter (h : f <= g) : blimsup u f p <= blimsup u g p
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
-/
theorem blimsup_monotone_filter (h : f ≤ g) : blimsup u f p ≤ blimsup u g p :=
  sInf_le_sInf fun _ ha => ha.filter_mono h
/-
**Filter.blimsup_and_le_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) <= blimsup u f p ⊓ b
limsup u f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Filter.blimsup_mono`：blimsup_mono (h : forall x, p x -> q x) : blimsup u
 f p <= blimsup u f q
-/
theorem blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p ⊓ blimsup u f q :=
  le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]
/-
**Filter.bliminf_sup_le_inf_aux_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_inf_aux_left : (blimsup u f fun x => p x ∧ q x) <= blimsup 
u f p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.blimsup_and_le_inf`：blimsup_and_le_inf : (blimsup u f fun x => p 
x ∧ q x) <= blimsup u f p ⊓ blimsup u f q
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem bliminf_sup_le_inf_aux_left :
    (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p :=
  blimsup_and_le_inf.trans inf_le_left

@[simp]
/-
**Filter.bliminf_sup_le_inf_aux_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_inf_aux_right : (blimsup u f fun x => p x ∧ q x) <= blimsup
 u f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.blimsup_and_le_inf`：blimsup_and_le_inf : (blimsup u f fun x => p 
x ∧ q x) <= blimsup u f p ⊓ blimsup u f q
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem bliminf_sup_le_inf_aux_right :
    (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f q :=
  blimsup_and_le_inf.trans inf_le_right
/-
**Filter.bliminf_sup_le_and** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_and : bliminf u f p ⊔ bliminf u f q <= bliminf u f fun x =>
 p x ∧ q x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_and_le_inf`：blimsup_and_le_inf : (blimsup u f fun x => p 
x ∧ q x) <= blimsup u f p ⊓ blimsup u f q
-/
theorem bliminf_sup_le_and : bliminf u f p ⊔ bliminf u f q ≤ bliminf u f fun x => p x ∧ q x :=
  blimsup_and_le_inf (α := αᵒᵈ)

@[simp]
/-
**Filter.bliminf_sup_le_and_aux_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_and_aux_left : bliminf u f p <= bliminf u f fun x => p x ∧ 
q x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Filter.bliminf_sup_le_and`：bliminf_sup_le_and : bliminf u f p ⊔ bliminf 
u f q <= bliminf u f fun x => p x ∧ q x
-/
theorem bliminf_sup_le_and_aux_left : bliminf u f p ≤ bliminf u f fun x => p x ∧ q x :=
  le_sup_left.trans bliminf_sup_le_and

@[simp]
/-
**Filter.bliminf_sup_le_and_aux_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_and_aux_right : bliminf u f q <= bliminf u f fun x => p x ∧
 q x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Filter.bliminf_sup_le_and`：bliminf_sup_le_and : bliminf u f p ⊔ bliminf 
u f q <= bliminf u f fun x => p x ∧ q x
-/
theorem bliminf_sup_le_and_aux_right : bliminf u f q ≤ bliminf u f fun x => p x ∧ q x :=
  le_sup_right.trans bliminf_sup_le_and

/-- See also `Filter.blimsup_or_eq_sup`. -/
/-
**Filter.blimsup_sup_le_or** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_sup_le_or : blimsup u f p ⊔ blimsup u f q <= blimsup u f fun x => 
p x ∨ q x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Filter.blimsup_mono`：blimsup_mono (h : forall x, p x -> q x) : blimsup u
 f p <= blimsup u f q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b

--- 原说明 ---
See also `Filter.blimsup_or_eq_sup`.
-/
theorem blimsup_sup_le_or : blimsup u f p ⊔ blimsup u f q ≤ blimsup u f fun x => p x ∨ q x :=
  sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)

@[simp]
/-
**Filter.bliminf_sup_le_or_aux_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_or_aux_left : blimsup u f p <= blimsup u f fun x => p x ∨ q
 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Filter.blimsup_sup_le_or`：blimsup_sup_le_or : blimsup u f p ⊔ blimsup u 
f q <= blimsup u f fun x => p x ∨ q x
-/
theorem bliminf_sup_le_or_aux_left : blimsup u f p ≤ blimsup u f fun x => p x ∨ q x :=
  le_sup_left.trans blimsup_sup_le_or

@[simp]
/-
**Filter.bliminf_sup_le_or_aux_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_sup_le_or_aux_right : blimsup u f q <= blimsup u f fun x => p x ∨ 
q x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Filter.blimsup_sup_le_or`：blimsup_sup_le_or : blimsup u f p ⊔ blimsup u 
f q <= blimsup u f fun x => p x ∨ q x
-/
theorem bliminf_sup_le_or_aux_right : blimsup u f q ≤ blimsup u f fun x => p x ∨ q x :=
  le_sup_right.trans blimsup_sup_le_or

/-- See also `Filter.bliminf_or_eq_inf`. -/
/-
**Filter.bliminf_or_le_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_or_le_inf : (bliminf u f fun x => p x ∨ q x) <= bliminf u f p ⊓ bl
iminf u f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_sup_le_or`：blimsup_sup_le_or : blimsup u f p ⊔ blimsup u 
f q <= blimsup u f fun x => p x ∨ q x

--- 原说明 ---
See also `Filter.bliminf_or_eq_inf`.
-/
theorem bliminf_or_le_inf : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p ⊓ bliminf u f q :=
  blimsup_sup_le_or (α := αᵒᵈ)

@[simp]
/-
**Filter.bliminf_or_le_inf_aux_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_or_le_inf_aux_left : (bliminf u f fun x => p x ∨ q x) <= bliminf u
 f p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.bliminf_or_le_inf`：bliminf_or_le_inf : (bliminf u f fun x => p x 
∨ q x) <= bliminf u f p ⊓ bliminf u f q
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem bliminf_or_le_inf_aux_left : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p :=
  bliminf_or_le_inf.trans inf_le_left

@[simp]
/-
**Filter.bliminf_or_le_inf_aux_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_or_le_inf_aux_right : (bliminf u f fun x => p x ∨ q x) <= bliminf 
u f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.bliminf_or_le_inf`：bliminf_or_le_inf : (bliminf u f fun x => p x 
∨ q x) <= bliminf u f p ⊓ bliminf u f q
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem bliminf_or_le_inf_aux_right : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f q :=
  bliminf_or_le_inf.trans inf_le_right
/-
**Filter._root_.OrderIso.apply_blimsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.apply_blimsup [CompleteLattice γ] (e : α ≃o γ) :
    e (blimsup u f p) = blimsup (e ∘ u) f p := by
  simp only [blimsup_eq, map_sInf, Function.comp_apply, e.image_eq_preimage_symm,
    Set.preimage_ofPred_eq, e.le_symm_apply]
/-
**Filter._root_.OrderIso.apply_bliminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.apply_bliminf [CompleteLattice γ] (e : α ≃o γ) :
    e (bliminf u f p) = bliminf (e ∘ u) f p :=
  e.dual.apply_blimsup
/-
**Filter._root_.sSupHom.apply_blimsup_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.sSupHom.apply_blimsup_le [CompleteLattice γ] (g : sSupHom α γ) :
    g (blimsup u f p) ≤ blimsup (g ∘ u) f p := by
  simp only [blimsup_eq_iInf_biSup, Function.comp]
  refine ((OrderHomClass.mono g).map_iInf₂_le _).trans ?_
  simp only [_root_.map_iSup, le_refl]
/-
**Filter._root_.sInfHom.le_apply_bliminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.sInfHom.le_apply_bliminf [CompleteLattice γ] (g : sInfHom α γ) :
    bliminf (g ∘ u) f p ≤ g (bliminf u f p) :=
  (sInfHom.dual g).apply_blimsup_le

end CompleteLattice

section CompleteDistribLattice

variable [CompleteDistribLattice α] {f : Filter β} {p q : β → Prop} {u : β → α}

/-
**Filter.limsup_sup_filter** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsup_sup_filter {g} : limsup u (f ⊔ g) = limsup u f ⊔ limsup u g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_sup_eq`：∀ {α : Type u} [inst : Order.Coframe α] {s : Set α} {b : α}
, sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sup_sInf_eq`：∀ {α : Type u} [inst : Order.Coframe α] {s : Set α} {a : α}
, a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Filter.limsup_le_limsup_of_le`：limsup_le_limsup_of_le {α β} [Conditional
lyCompleteLattice β] {f g : Filter α} (h : f <= g) {u : α -> β} (hf : f.IsCoboun
dedUnder (· <= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
lemma limsup_sup_filter {g} : limsup u (f ⊔ g) = limsup u f ⊔ limsup u g := by
  refine le_antisymm ?_
    (sup_le (limsup_le_limsup_of_le le_sup_left) (limsup_le_limsup_of_le le_sup_right))
  simp_rw [limsup_eq, sInf_sup_eq, sup_sInf_eq, mem_ofPred_eq, le_iInf₂_iff]
  intro a ha b hb
  exact sInf_le ⟨ha.mono fun _ h ↦ h.trans le_sup_left, hb.mono fun _ h ↦ h.trans le_sup_right⟩
/-
**Filter.liminf_sup_filter** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：liminf_sup_filter {g} : liminf u (f ⊔ g) = liminf u f ⊓ liminf u g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.limsup_sup_filter`：limsup_sup_filter {g} : limsup u (f ⊔ g) = lim
sup u f ⊔ limsup u g
-/
lemma liminf_sup_filter {g} : liminf u (f ⊔ g) = liminf u f ⊓ liminf u g :=
  limsup_sup_filter (α := αᵒᵈ)

@[simp]
/-
**Filter.blimsup_or_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ bli
msup u f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.blimsup_eq_limsup`：blimsup_eq_limsup {f : Filter β} {u : β -> α} 
{p : β -> Prop} : blimsup u f p = limsup u (f ⊓ 𝓟 {x | p x})
· 使用定理 `Filter.sup_principal`：sup_principal {s t : Set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s uni
on t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q := by
  simp only [blimsup_eq_limsup, ← limsup_sup_filter, ← inf_sup_left, sup_principal, ofPred_or]

@[simp]
/-
**Filter.bliminf_or_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bli
minf u f q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.blimsup_or_eq_sup`：blimsup_or_eq_sup : (blimsup u f fun x => p x 
∨ q x) = blimsup u f p ⊔ blimsup u f q
-/
theorem bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
  blimsup_or_eq_sup (α := αᵒᵈ)

@[simp]
/-
**Filter.blimsup_sup_not** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬p ·) = limsup u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.blimsup_true`：blimsup_true (f : Filter β) (u : β -> α) : (blimsup
 u f fun _ => True) = limsup u f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬p ·) = limsup u f := by
  simp_rw [← blimsup_or_eq_sup, or_not, blimsup_true]

@[simp]
/-
**Filter.bliminf_inf_not** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：bliminf_inf_not : bliminf u f p ⊓ bliminf u f (¬p ·) = liminf u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.blimsup_sup_not`：blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬
p ·) = limsup u f
-/
lemma bliminf_inf_not : bliminf u f p ⊓ bliminf u f (¬p ·) = liminf u f :=
  blimsup_sup_not (α := αᵒᵈ)

@[simp]
/-
**Filter.blimsup_not_sup** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：blimsup_not_sup : blimsup u f (¬p ·) ⊔ blimsup u f p = limsup u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Filter.blimsup_sup_not`：blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬
p ·) = limsup u f
-/
lemma blimsup_not_sup : blimsup u f (¬p ·) ⊔ blimsup u f p = limsup u f := by
  simpa only [not_not] using blimsup_sup_not (p := (¬p ·))

@[simp]
/-
**Filter.bliminf_not_inf** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：bliminf_not_inf : bliminf u f (¬p ·) ⊓ bliminf u f p = liminf u f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.blimsup_not_sup`：blimsup_not_sup : blimsup u f (¬p ·) ⊔ blimsup u
 f p = limsup u f
-/
lemma bliminf_not_inf : bliminf u f (¬p ·) ⊓ bliminf u f p = liminf u f :=
  blimsup_not_sup (α := αᵒᵈ)
/-
**Filter.limsup_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsup_piecewise {s : Set β} [DecidablePred (· in s)] {v} : limsup (s.piec
ewise u v) f = blimsup u f (· in s) ⊔ blimsup v f (· ∉ s)
参数：· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.blimsup_sup_not`：blimsup_sup_not : blimsup u f p ⊔ blimsup u f (¬
p ·) = limsup u f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Filter.blimsup_congr`：blimsup_congr {f : Filter β} {u v : β -> α} {p : β
 -> Prop} (h : forallᶠ a in f, p a -> u a = v a) : blimsup u f p = blimsup v f p
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma limsup_piecewise {s : Set β} [DecidablePred (· ∈ s)] {v} :
    limsup (s.piecewise u v) f = blimsup u f (· ∈ s) ⊔ blimsup v f (· ∉ s) := by
  rw [← blimsup_sup_not (p := (· ∈ s))]
  refine congr_arg₂ _ (blimsup_congr ?_) (blimsup_congr ?_) <;>
    filter_upwards with _ h using by simp [h]
/-
**Filter.liminf_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：liminf_piecewise {s : Set β} [DecidablePred (· in s)] {v} : liminf (s.piec
ewise u v) f = bliminf u f (· in s) ⊓ bliminf v f (· ∉ s)
参数：· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.limsup_piecewise`：limsup_piecewise {s : Set β} [DecidablePred (· 
in s)] {v} : limsup (s.piecewise u v) f = blimsup u f (· in s) ⊔ blimsup v f (· 
∉ s)
-/
lemma liminf_piecewise {s : Set β} [DecidablePred (· ∈ s)] {v} :
    liminf (s.piecewise u v) f = bliminf u f (· ∈ s) ⊓ bliminf v f (· ∉ s) :=
  limsup_piecewise (α := αᵒᵈ)
/-
**Filter.sup_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) 
f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.limsup_eq_iInf_iSup`：limsup_eq_iInf_iSup {f : Filter β} {u : β ->
 α} : limsup u f = ⨅ s in f, ⨆ a in s, u a
· 使用定理 `sup_iInf₂_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : Orde
r.Coframe α] {f : (i : ι) → κ i → α} (a : α),   a ⊔ ⨅ i, ⨅ j, f i j = ⨅ i, ⨅ j, 
a …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_sup_eq`：iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `biSup_const`：biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i in 
s, a = a
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
-/
theorem sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f := by
  simp only [limsup_eq_iInf_iSup, iSup_sup_eq, sup_iInf₂_eq]
  congr; ext s; congr; ext hs; congr
  exact (biSup_const (nonempty_of_mem hs)).symm
/-
**Filter.inf_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) 
f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.sup_limsup`：sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsu
p (fun x => a ⊔ u x) f
-/
theorem inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f :=
  sup_limsup (α := αᵒᵈ) a
/-
**Filter.sup_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.liminf_eq_iSup_iInf`：liminf_eq_iSup_iInf {f : Filter β} {u : β ->
 α} : liminf u f = ⨆ s in f, ⨅ a in s, u a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `biSup_sup`：biSup_sup {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h
 : exists i, p i) : (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf₂_sup_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : Orde
r.Coframe α] {f : (i : ι) → κ i → α} (a : α),   (⨅ i, ⨅ j, f i j) ⊔ a = ⨅ i, ⨅ j
, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f := by
  simp only [liminf_eq_iSup_iInf]
  rw [sup_comm, biSup_sup (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [iInf₂_sup_eq, sup_comm (a := a)]
/-
**Filter.inf_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.sup_liminf`：sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x =
> a ⊔ u x) f
-/
theorem inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f :=
  sup_liminf (α := αᵒᵈ) a

end CompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] (f : Filter β) (u : β → α)

/-
**Filter.limsup_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_eq_iInf_iSup`：limsup_eq_iInf_iSup {f : Filter β} {u : β ->
 α} : limsup u f = ⨅ s in f, ⨆ a in s, u a
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
· 使用定理 `Filter.liminf_eq_iSup_iInf`：liminf_eq_iSup_iInf {f : Filter β} {u : β ->
 α} : liminf u f = ⨆ s in f, ⨅ a in s, u a
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]
/-
**Filter.liminf_compl** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_compl : (liminf u f)ᶜ = limsup (compl ∘ u) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.liminf_eq_iSup_iInf`：liminf_eq_iSup_iInf {f : Filter β} {u : β ->
 α} : liminf u f = ⨆ s in f, ⨅ a in s, u a
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
· 使用定理 `Filter.limsup_eq_iInf_iSup`：limsup_eq_iInf_iSup {f : Filter β} {u : β ->
 α} : limsup u f = ⨅ s in f, ⨆ a in s, u a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liminf_compl : (liminf u f)ᶜ = limsup (compl ∘ u) f := by
  simp only [limsup_eq_iInf_iSup, compl_iInf, compl_iSup, liminf_eq_iSup_iInf, Function.comp_apply]
/-
**Filter.limsup_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.limsup_eq_iInf_iSup`：limsup_eq_iInf_iSup {f : Filter β} {u : β ->
 α} : limsup u f = ⨅ s in f, ⨆ a in s, u a
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `biInf_inf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {p
 : ι → Prop} {f : (i : ι) → p i → α} {a : α},   (∃ i, p i) → (⨅ i, ⨅ (h : p i),…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_iSup₂_eq`：∀ {α : Type u} {ι : Sort w} {κ : ι → Sort w'} [inst : Orde
r.Frame α] {f : (i : ι) → κ i → α} (a : α),   a ⊓ ⨆ i, ⨆ j, f i j = ⨆ i, ⨆ j, a 
⊓ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f := by
  simp only [limsup_eq_iInf_iSup, _root_.sdiff_eq]
  rw [biInf_inf (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]
/-
**Filter.liminf_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a
) f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Filter.inf_liminf`：inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = limin
f (fun x => a ⊓ u x) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a) f := by
  simp only [_root_.sdiff_eq, inf_comm _ aᶜ, inf_liminf]
/-
**Filter.sdiff_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b
) f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.sup_limsup`：sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsu
p (fun x => a ⊔ u x) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.liminf_compl`：liminf_compl : (liminf u f)ᶜ = limsup (compl ∘ u) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, liminf_compl, comp_def, compl_inf, compl_compl, sup_limsup]
/-
**Filter.sdiff_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.sup_liminf`：sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x =
> a ⊔ u x) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.limsup_compl`：limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f := by
  rw [← compl_inj_iff]
  simp only [_root_.sdiff_eq, limsup_compl, comp_def, compl_inf, compl_compl, sup_liminf]

end CompleteBooleanAlgebra

section SetLattice

variable {p : ι → Prop} {s : ι → Set α} {𝓕 : Filter ι} {a : α}

/-
**Filter.mem_liminf_iff_eventually_mem** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：mem_liminf_iff_eventually_mem : (a in liminf s 𝓕) ↔ (forallᶠ i in 𝓕, a in 
s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.liminf_eq_iSup_iInf`：liminf_eq_iSup_iInf {f : Filter β} {u : β ->
 α} : liminf u f = ⨆ s in f, ⨅ a in s, u a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
lemma mem_liminf_iff_eventually_mem : (a ∈ liminf s 𝓕) ↔ (∀ᶠ i in 𝓕, a ∈ s i) := by
  simpa only [liminf_eq_iSup_iInf, iSup_eq_iUnion, iInf_eq_iInter, mem_iUnion, mem_iInter]
    using ⟨fun ⟨S, hS, hS'⟩ ↦ mem_of_superset hS (by tauto), fun h ↦ ⟨{i | a ∈ s i}, h, by tauto⟩⟩
/-
**Filter.mem_limsup_iff_frequently_mem** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：mem_limsup_iff_frequently_mem : (a in limsup s 𝓕) ↔ (existsᶠ i in 𝓕, a in 
s i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.limsup_compl`：limsup_compl : (limsup u f)ᶜ = liminf (compl ∘ u) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_limsup_iff_frequently_mem : (a ∈ limsup s 𝓕) ↔ (∃ᶠ i in 𝓕, a ∈ s i) := by
  simp only [Filter.Frequently, iff_not_comm, ← mem_compl_iff, limsup_compl, comp_apply,
    mem_liminf_iff_eventually_mem]
/-
**Filter.cofinite.blimsup_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.cofinite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → Set α},   Filter.b
limsup s Filter.cofinite p = {x | {n | p n ∧ x ∈ s n}.Infinite}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem cofinite.blimsup_set_eq :
    blimsup s cofinite p = { x | { n | p n ∧ x ∈ s n }.Infinite } := by
  simp only [blimsup_eq, eventually_cofinite, not_forall, sInf_eq_sInter, exists_prop]
  ext x
  refine ⟨fun h => ?_, fun hx t h => ?_⟩ <;> contrapose h
  · simp only [mem_sInter, mem_ofPred_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
  · exact hx.mono fun i hi => ⟨hi.1, fun hit => h (hit hi.2)⟩
/-
**Filter.cofinite.bliminf_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.cofinite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {p : ι → Prop} {s : ι → Set α},   Filter.b
liminf s Filter.cofinite p = {x | {n | p n ∧ x ∉ s n}.Finite}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.bliminf_eq_iSup_biInf`：bliminf_eq_iSup_biInf {f : Filter β} {p : 
β -> Prop} {u : β -> α} : bliminf u f p = ⨆ s in f, ⨅ (b) (_ : p b ∧ b in s), u 
b
· 使用定理 `compl_iSup`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iSup f)ᶜ = ⨅ i, (f i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `compl_iInf`：∀ {α : Type u} {ι : Sort w} [inst : CompleteBooleanAlgebra α
] {f : ι → α}, (iInf f)ᶜ = ⨆ i, (f i)ᶜ
· 使用定理 `Filter.cofinite.blimsup_set_eq`：∀ {α : Type u_1} {ι : Type u_4} {p : ι →
 Prop} {s : ι → Set α},   Filter.blimsup s Filter.cofinite p = {x | {n | p n ∧ x
 ∈ s n}.Infinite}
-/
theorem cofinite.bliminf_set_eq : bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite } := by
  rw [← compl_inj_iff]
  simp only [bliminf_eq_iSup_biInf, compl_iInf, compl_iSup, ← blimsup_eq_iInf_biSup,
    cofinite.blimsup_set_eq]
  rfl

/-- In other words, `limsup cofinite s` is the set of elements lying inside the family `s`
infinitely often. -/
/-
**Filter.cofinite.limsup_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.cofinite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {s : ι → Set α}, Filter.limsup s Filter.co
finite = {x | {n | x ∈ s n}.Infinite}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.blimsup_true`：blimsup_true (f : Filter β) (u : β -> α) : (blimsup
 u f fun _ => True) = limsup u f
· 使用定理 `Filter.cofinite.blimsup_set_eq`：∀ {α : Type u_1} {ι : Type u_4} {p : ι →
 Prop} {s : ι → Set α},   Filter.blimsup s Filter.cofinite p = {x | {n | p n ∧ x
 ∈ s n}.Infinite}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In other words, `limsup cofinite s` is the set of elements lying inside the fami
ly `s`
infinitely often.
-/
theorem cofinite.limsup_set_eq : limsup s cofinite = { x | { n | x ∈ s n }.Infinite } := by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and]

/-- In other words, `liminf cofinite s` is the set of elements lying outside the family `s`
finitely often. -/
/-
**Filter.cofinite.liminf_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.cofinite`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {s : ι → Set α}, Filter.liminf s Filter.co
finite = {x | {n | x ∉ s n}.Finite}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.bliminf_true`：bliminf_true (f : Filter β) (u : β -> α) : (bliminf
 u f fun _ => True) = liminf u f
· 使用定理 `Filter.cofinite.bliminf_set_eq`：∀ {α : Type u_1} {ι : Type u_4} {p : ι →
 Prop} {s : ι → Set α},   Filter.bliminf s Filter.cofinite p = {x | {n | p n ∧ x
 ∉ s n}.Finite}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In other words, `liminf cofinite s` is the set of elements lying outside the fam
ily `s`
finitely often.
-/
theorem cofinite.liminf_set_eq : liminf s cofinite = { x | { n | x ∉ s n }.Finite } := by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and]
/-
**Filter.exists_forall_mem_of_hasBasis_mem_blimsup** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
形式化陈述：exists_forall_mem_of_hasBasis_mem_blimsup {l : Filter β} {b : ι -> Set β} 
{q : ι -> Prop} (hl : l.HasBasis q b) {u : β -> Set α} {p : β -> Prop} {x : α} (
hx : x in blimsup u l p) : exists f : { i | q i } -> β, forall i, x in u (f i) ∧
 p (f i) ∧ f i in b i
参数：hl : l.HasBasis q b；hx : x in blimsup u l p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.blimsup_eq_iInf_biSup`：blimsup_eq_iInf_biSup {f : Filter β} {p : 
β -> Prop} {u : β -> α} : blimsup u f p = ⨅ s in f, ⨆ (b) (_ : p b ∧ b in s), u 
b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem exists_forall_mem_of_hasBasis_mem_blimsup {l : Filter β} {b : ι → Set β} {q : ι → Prop}
    (hl : l.HasBasis q b) {u : β → Set α} {p : β → Prop} {x : α} (hx : x ∈ blimsup u l p) :
    ∃ f : { i | q i } → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i := by
  rw [blimsup_eq_iInf_biSup] at hx
  simp only [iSup_eq_iUnion, iInf_eq_iInter, mem_iInter, mem_iUnion, exists_prop] at hx
  choose g hg hg' using hx
  refine ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨?_, ?_⟩⟩
  · exact hg' (b i) (hl.mem_of_mem i.2)
  · exact hg (b i) (hl.mem_of_mem i.2)
/-
**Filter.exists_forall_mem_of_hasBasis_mem_blimsup'** 是 Mathlib 中的一个定理，位于命名空间 `F
ilter`。
形式化陈述：exists_forall_mem_of_hasBasis_mem_blimsup' {l : Filter β} {b : ι -> Set β}
 (hl : l.HasBasis (fun _ => True) b) {u : β -> Set α} {p : β -> Prop} {x : α} (h
x : x in blimsup u l p) : exists f : ι -> β, forall i, x in u (f i) ∧ p (f i) ∧ 
f i in b i
参数：hl : l.HasBasis (fun _ => True) b；hx : x in blimsup u l p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_forall_mem_of_hasBasis_mem_blimsup`：exists_forall_mem_of_h
asBasis_mem_blimsup {l : Filter β} {b : ι -> Set β} {q : ι -> Prop} (hl : l.HasB
asis q b) {u : β -> Set α} {p : β -> P…
· 使用定理 `trivial`：True
-/
theorem exists_forall_mem_of_hasBasis_mem_blimsup' {l : Filter β} {b : ι → Set β}
    (hl : l.HasBasis (fun _ => True) b) {u : β → Set α} {p : β → Prop} {x : α}
    (hx : x ∈ blimsup u l p) : ∃ f : ι → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i := by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_hasBasis_mem_blimsup hl hx
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩

end SetLattice

section ConditionallyCompleteLinearOrder

/-
**Filter.frequently_lt_of_lt_limsSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_lt_of_lt_limsSup {f : Filter α} [ConditionallyCompleteLinearOrd
er α] {a : α} (hf : f.IsCobounded (· <= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.limsSup_le_of_le`：limsSup_le_of_le {f : Filter α} {a} (hf : f.IsC
obounded (· <= ·)
-/
theorem frequently_lt_of_lt_limsSup {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≤ ·) := by isBoundedDefault)
    (h : a < limsSup f) : ∃ᶠ n in f, a < n := by
  contrapose! h
  exact limsSup_le_of_le hf h
/-
**Filter.frequently_lt_of_limsInf_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_lt_of_limsInf_lt {f : Filter α} [ConditionallyCompleteLinearOrd
er α] {a : α} (hf : f.IsCobounded (· >= ·)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.frequently_lt_of_lt_limsSup`：frequently_lt_of_lt_limsSup {f : Fil
ter α} [ConditionallyCompleteLinearOrder α] {a : α} (hf : f.IsCobounded (· <= ·)
-/
theorem frequently_lt_of_limsInf_lt {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (h : limsInf f < a) : ∃ᶠ n in f, n < a :=
  frequently_lt_of_lt_limsSup (α := OrderDual α) hf h
/-
**Filter.eventually_lt_of_lt_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrde
r β] {u : α -> β} {b : β} (h : b < liminf u f) (hu : f.IsBoundedUnder (· >= ·) u
参数：h : b < liminf u f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : b < liminf u f)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    ∀ᶠ a in f, b < u a := by
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (_ : c ∈ { c : β | ∀ᶠ n : α in f, c ≤ u n }), b < c := by
    simp_rw [exists_prop]
    exact exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx
/-
**Filter.eventually_lt_of_limsup_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrde
r β] {u : α -> β} {b : β} (h : limsup u f < b) (hu : f.IsBoundedUnder (· <= ·) u
参数：h : limsup u f < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
-/
theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : limsup u f < b)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    ∀ᶠ a in f, u a < b :=
  eventually_lt_of_lt_liminf (β := βᵒᵈ) h hu

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

/-- If `Filter.limsup u atTop ≤ x`, then for all `ε > 0`, eventually we have `u b < x + ε`. -/
/-
**Filter.eventually_lt_add_pos_of_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_lt_add_pos_of_limsup_le [Preorder β] [AddZeroClass α] [AddLeftS
trictMono α] {x ε : α} {u : β -> α} (hu_bdd : IsBoundedUnder LE.le atTop u) (hu 
: Filter.limsup u atTop <= x) (hε : 0 < ε) : forallᶠ b : β in atTop, u b < x + ε
参数：hu_bdd : IsBoundedUnder LE.le atTop u；hu : Filter.limsup u atTop <= x；hε : 0 
< ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b

--- 原说明 ---
If `Filter.limsup u atTop ≤ x`, then for all `ε > 0`, eventually we have `u b < 
x + ε`.
-/
theorem eventually_lt_add_pos_of_limsup_le [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
    {x ε : α} {u : β → α} (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop ≤ x)
    (hε : 0 < ε) :
    ∀ᶠ b : β in atTop, u b < x + ε :=
  eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (lt_add_of_pos_right x hε)) hu_bdd

/-- If `x ≤ Filter.liminf u atTop`, then for all `ε < 0`, eventually we have `x + ε < u b`. -/
/-
**Filter.eventually_add_neg_lt_of_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_add_neg_lt_of_le_liminf [Preorder β] [AddZeroClass α] [AddLeftS
trictMono α] {x ε : α} {u : β -> α} (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu 
: x <= Filter.liminf u atTop) (hε : ε < 0) : forallᶠ b : β in atTop, x + ε < u b
参数：hu_bdd : IsBoundedUnder GE.ge atTop u；hu : x <= Filter.liminf u atTop；hε : ε 
< 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_of_neg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, b < 0 → a + b < a

--- 原说明 ---
If `x ≤ Filter.liminf u atTop`, then for all `ε < 0`, eventually we have `x + ε 
< u b`.
-/
theorem eventually_add_neg_lt_of_le_liminf [Preorder β] [AddZeroClass α] [AddLeftStrictMono α]
    {x ε : α} {u : β → α} (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x ≤ Filter.liminf u atTop)
    (hε : ε < 0) :
    ∀ᶠ b : β in atTop, x + ε < u b :=
  eventually_lt_of_lt_liminf (lt_of_lt_of_le (add_lt_of_neg_right x hε) hu) hu_bdd

/-- If `Filter.limsup u atTop ≤ x`, then for all `ε > 0`, there exists a positive natural
number `n` such that `u n < x + ε`. -/
/-
**Filter.exists_lt_of_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_lt_of_limsup_le [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u
 : Nat -> α} (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop
 <= x) (hε : 0 < ε) : exists n : PNat, u n < x + ε
参数：hu_bdd : IsBoundedUnder LE.le atTop u；hu : Filter.limsup u atTop <= x；hε : 0 
< ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_lt_add_pos_of_limsup_le`：eventually_lt_add_pos_of_lims
up_le [Preorder β] [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : β -> α}
 (hu_bdd : IsBoundedUnder LE.le…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
If `Filter.limsup u atTop ≤ x`, then for all `ε > 0`, there exists a positive na
tural
number `n` such that `u n < x + ε`.
-/
theorem exists_lt_of_limsup_le [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : ℕ → α}
    (hu_bdd : IsBoundedUnder LE.le atTop u) (hu : Filter.limsup u atTop ≤ x) (hε : 0 < ε) :
    ∃ n : PNat, u n < x + ε := by
  have h : ∀ᶠ n : ℕ in atTop, u n < x + ε := eventually_lt_add_pos_of_limsup_le hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩

/-- If `x ≤ Filter.liminf u atTop`, then for all `ε < 0`, there exists a positive natural
number `n` such that ` x + ε < u n`. -/
/-
**Filter.exists_lt_of_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_lt_of_le_liminf [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u
 : Nat -> α} (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x <= Filter.liminf u 
atTop) (hε : ε < 0) : exists n : PNat, x + ε < u n
参数：hu_bdd : IsBoundedUnder GE.ge atTop u；hu : x <= Filter.liminf u atTop；hε : ε 
< 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_add_neg_lt_of_le_liminf`：eventually_add_neg_lt_of_le_l
iminf [Preorder β] [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : β -> α}
 (hu_bdd : IsBoundedUnder GE.ge…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
If `x ≤ Filter.liminf u atTop`, then for all `ε < 0`, there exists a positive na
tural
number `n` such that ` x + ε < u n`.
-/
theorem exists_lt_of_le_liminf [AddZeroClass α] [AddLeftStrictMono α] {x ε : α} {u : ℕ → α}
    (hu_bdd : IsBoundedUnder GE.ge atTop u) (hu : x ≤ Filter.liminf u atTop) (hε : ε < 0) :
    ∃ n : PNat, x + ε < u n := by
  have h : ∀ᶠ n : ℕ in atTop, x + ε < u n := eventually_add_neg_lt_of_le_liminf hu_bdd hu hε
  simp only [eventually_atTop] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨⟨n + 1, Nat.succ_pos _⟩, hn (n + 1) (Nat.le_succ _)⟩
end ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder β] {f : Filter α} {u : α → β}

/-
**Filter.frequently_lt_of_lt_limsup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_lt_of_lt_limsup {b : β} (hu : f.IsCoboundedUnder (· <= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.limsSup_le_of_le`：limsSup_le_of_le {f : Filter α} {a} (hf : f.IsC
obounded (· <= ·)
-/
theorem frequently_lt_of_lt_limsup {b : β}
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h : b < limsup u f) : ∃ᶠ x in f, b < u x := by
  contrapose! h
  apply limsSup_le_of_le hu
  simpa using h
/-
**Filter.frequently_lt_of_liminf_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_lt_of_liminf_lt {b : β} (hu : f.IsCoboundedUnder (· >= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
-/
theorem frequently_lt_of_liminf_lt {b : β}
    (hu : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : liminf u f < b) : ∃ᶠ x in f, u x < b :=
  frequently_lt_of_lt_limsup (β := βᵒᵈ) hu h
/-
**Filter.limsup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_gt_iff_le`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ 
⦃c : α⦄, a < c → b < c) ↔ b ≤ a
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    limsup u f ≤ x ↔ ∀ y > x, ∀ᶠ a in f, u a < y := by
  refine ⟨fun h _ h' ↦ eventually_lt_of_limsup_lt (h.trans_lt h') h₂, fun h ↦ ?_⟩
  --Two cases: Either `x` is a cluster point from above, or it is not.
  --In the first case, we use `forall_gt_iff_le` and split an interval.
  --In the second case, the function `u` must eventually be smaller or equal to `x`.
  by_cases h' : ∀ y > x, ∃ z, x < z ∧ z < y
  · rw [← forall_gt_iff_le]
    intro y x_y
    rcases h' y x_y with ⟨z, x_z, z_y⟩
    exact (limsup_le_of_le h₁ ((h z x_z).mono (fun _ ↦ le_of_lt))).trans_lt z_y
  · apply limsup_le_of_le h₁
    push +distrib Not at h'
    rcases h' with ⟨z, x_z, hz⟩
    exact (h z x_z).mono <| fun w hw ↦ (or_iff_left (not_le_of_gt hw)).1 (hz (u w))

/-- A version of `limsup_le_iff` with large inequalities in densely ordered spaces -/
/-
**Filter.limsup_le_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：limsup_le_iff' [DenselyOrdered β] {x : β} (h₁ : IsCoboundedUnder (· <= ·) 
f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_gt_iff_le`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ 
⦃c : α⦄, a < c → b < c) ↔ b ≤ a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Filter.limsup_le_of_le`：limsup_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· <= ·) u

--- 原说明 ---
A version of `limsup_le_iff` with large inequalities in densely ordered spaces
-/
lemma limsup_le_iff' [DenselyOrdered β] {x : β}
    (h₁ : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    limsup u f ≤ x ↔ ∀ y > x, ∀ᶠ (a : α) in f, u a ≤ y := by
  refine ⟨fun h _ h' ↦ (eventually_lt_of_limsup_lt (h.trans_lt h') h₂).mono fun _ ↦ le_of_lt, ?_⟩
  rw [← forall_gt_iff_le]
  intro h y x_y
  obtain ⟨z, x_z, z_y⟩ := exists_between x_y
  exact (limsup_le_of_le h₁ (h z x_z)).trans_lt z_y
/-
**Filter.le_limsup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· <= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_lt_iff_le`：forall_lt_iff_le : (forall ⦃c⦄, c < a -> c < b) ↔ a <=
 b
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    x ≤ limsup u f ↔ ∀ y < x, ∃ᶠ a in f, y < u a := by
  refine ⟨fun h _ h' ↦ frequently_lt_of_lt_limsup h₁ (h'.trans_le h), fun h ↦ ?_⟩
  --Two cases: Either `x` is a cluster point from below, or it is not.
  --In the first case, we use `forall_lt_iff_le` and split an interval.
  --In the second case, the function `u` must frequently be larger or equal to `x`.
  by_cases h' : ∀ y < x, ∃ z, y < z ∧ z < x
  · rw [← forall_lt_iff_le]
    intro y y_x
    obtain ⟨z, y_z, z_x⟩ := h' y y_x
    exact y_z.trans_le (le_limsup_of_frequently_le ((h z z_x).mono (fun _ ↦ le_of_lt)) h₂)
  · apply le_limsup_of_frequently_le _ h₂
    push +distrib Not at h'
    rcases h' with ⟨z, z_x, hz⟩
    exact (h z z_x).mono <| fun w hw ↦ (or_iff_right (not_le_of_gt hw)).1 (hz (u w))

/-- A version of `le_limsup_iff` with large inequalities in densely ordered spaces. -/
/-
**Filter.le_limsup_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：le_limsup_iff' [DenselyOrdered β] {x : β} (h₁ : f.IsCoboundedUnder (· <= ·
) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_lt_iff_le`：forall_lt_iff_le : (forall ⦃c⦄, c < a -> c < b) ↔ a <=
 b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u

--- 原说明 ---
A version of `le_limsup_iff` with large inequalities in densely ordered spaces.
-/
lemma le_limsup_iff' [DenselyOrdered β] {x : β}
    (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault) :
    x ≤ limsup u f ↔ ∀ y < x, ∃ᶠ a in f, y ≤ u a := by
  refine ⟨fun h _ h' ↦ (frequently_lt_of_lt_limsup h₁ (h'.trans_le h)).mono fun _ ↦ le_of_lt, ?_⟩
  rw [← forall_lt_iff_le]
  intro h y y_x
  obtain ⟨z, y_z, z_x⟩ := exists_between y_x
  exact y_z.trans_le (le_limsup_of_frequently_le (h z z_x) h₂)
/-
**Filter.le_liminf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
-/
theorem le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    x ≤ liminf u f ↔ ∀ y < x, ∀ᶠ a in f, y < u a := limsup_le_iff (β := βᵒᵈ) h₁ h₂

/-- A version of `le_liminf_iff` with large inequalities in densely ordered spaces. -/
/-
**Filter.le_liminf_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_liminf_iff' [DenselyOrdered β] {x : β} (h₁ : f.IsCoboundedUnder (· >= ·
) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.limsup_le_iff'`：limsup_le_iff' [DenselyOrdered β] {x : β} (h₁ : I
sCoboundedUnder (· <= ·) f u

--- 原说明 ---
A version of `le_liminf_iff` with large inequalities in densely ordered spaces.
-/
theorem le_liminf_iff' [DenselyOrdered β] {x : β}
    (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    x ≤ liminf u f ↔ ∀ y < x, ∀ᶠ a in f, y ≤ u a := limsup_le_iff' (β := βᵒᵈ) h₁ h₂
/-
**Filter.liminf_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· >= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
-/
theorem liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ x ↔ ∀ y > x, ∃ᶠ a in f, u a < y := le_limsup_iff (β := βᵒᵈ) h₁ h₂

/-- A version of `liminf_le_iff` with large inequalities in densely ordered spaces. -/
/-
**Filter.liminf_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：liminf_le_iff' [DenselyOrdered β] {x : β} (h₁ : f.IsCoboundedUnder (· >= ·
) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.le_limsup_iff'`：le_limsup_iff' [DenselyOrdered β] {x : β} (h₁ : f
.IsCoboundedUnder (· <= ·) u

--- 原说明 ---
A version of `liminf_le_iff` with large inequalities in densely ordered spaces.
-/
theorem liminf_le_iff' [DenselyOrdered β] {x : β}
    (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    liminf u f ≤ x ↔ ∀ y > x, ∃ᶠ a in f, u a ≤ y := le_limsup_iff' (β := βᵒᵈ) h₁ h₂
/-
**Filter.liminf_le_limsup_of_frequently_le** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：liminf_le_limsup_of_frequently_le {v : α -> β} (h : existsᶠ x in f, u x <=
 v x) (h₁ : f.IsBoundedUnder (· >= ·) u
参数：h : existsᶠ x in f, u x <= v x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.frequently_bot`：frequently_bot {p : α -> Prop} : ¬existsᶠ x in ⊥,
 p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.IsBoundedUnder.eventually_le`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] {f : Filter β} {u : β → α},   Filter.IsBoundedUnder (fun x1 x2 
=> x1 ≤ x2) f u → ∃ a, ∀ᶠ…
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_le`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 u x ≤ a) → Filter.IsCobounded…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.IsBoundedUnder.eventually_ge`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] {f : Filter β} {u : β → α},   Filter.IsBoundedUnder (fun x1 x2 
=> x2 ≤ x1) f u → ∃ a, ∀ᶠ…
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_ge`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 a ≤ u x) → Filter.IsCobounded…
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
lemma liminf_le_limsup_of_frequently_le {v : α → β} (h : ∃ᶠ x in f, u x ≤ v x)
    (h₁ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) :
    liminf u f ≤ limsup v f := by
  rcases f.eq_or_neBot with rfl | _
  · exact (frequently_bot h).rec
  have h₃ : f.IsCoboundedUnder (· ≥ ·) u := by
    obtain ⟨a, ha⟩ := h₂.eventually_le
    apply IsCoboundedUnder.of_frequently_le (a := a)
    exact (h.and_eventually ha).mono fun x ⟨u_x, v_x⟩ ↦ u_x.trans v_x
  have h₄ : f.IsCoboundedUnder (· ≤ ·) v := by
    obtain ⟨a, ha⟩ := h₁.eventually_ge
    apply IsCoboundedUnder.of_frequently_ge (a := a)
    exact (ha.and_frequently h).mono fun x ⟨u_x, v_x⟩ ↦ u_x.trans v_x
  refine (le_limsup_iff h₄ h₂).2 fun y y_v ↦ ?_
  have := (le_liminf_iff h₃ h₁).1 (le_refl (liminf u f)) y y_v
  exact (h.and_eventually this).mono fun x ⟨ux_vx, y_ux⟩ ↦ y_ux.trans_le ux_vx

variable [ConditionallyCompleteLinearOrder α] {f : Filter α} {b : α}

-- The linter erroneously claims that I'm not referring to `c`
set_option linter.unusedVariables false in
/-
**Filter.lt_mem_sets_of_limsSup_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lt_mem_sets_of_limsSup_lt (h : f.IsBounded (· <= ·)) (l : f.limsSup < b) :
 forallᶠ a in f, a < b
参数：h : f.IsBounded (· <= ·)；l : f.limsSup < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
-/
theorem lt_mem_sets_of_limsSup_lt (h : f.IsBounded (· ≤ ·)) (l : f.limsSup < b) :
    ∀ᶠ a in f, a < b :=
  let ⟨c, (h : ∀ᶠ a in f, a ≤ c), hcb⟩ := exists_lt_of_csInf_lt h l
  mem_of_superset h fun _a => hcb.trans_le'
/-
**Filter.gt_mem_sets_of_limsInf_gt** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：gt_mem_sets_of_limsInf_gt : f.IsBounded (· >= ·) -> b < f.limsInf -> foral
lᶠ a in f, b < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.lt_mem_sets_of_limsSup_lt`：lt_mem_sets_of_limsSup_lt (h : f.IsBou
nded (· <= ·)) (l : f.limsSup < b) : forallᶠ a in f, a < b
-/
theorem gt_mem_sets_of_limsInf_gt : f.IsBounded (· ≥ ·) → b < f.limsInf → ∀ᶠ a in f, b < a :=
  @lt_mem_sets_of_limsSup_lt αᵒᵈ _ _ _

section Classical

open scoped Classical in
/-- Given an indexed family of sets `s j` over `j : Subtype p` and a function `f`, then
`liminfReparam j` is equal to `j` if `f` is bounded below on `s j`, and otherwise to some
index `k` such that `f` is bounded below on `s k` (if there exists one).
To ensure good measurability behavior, this index `k` is chosen as the minimal suitable index.
This function is used to write down a liminf in a measurable way,
in `Filter.HasBasis.liminf_eq_ciSup_ciInf` and `Filter.HasBasis.liminf_eq_ite`. -/
/-
**Filter.liminfReparam** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：liminfReparam (f : ι -> α) (s : ι' -> Set ι) (p : ι' -> Prop) [Countable (
Subtype p)] [Nonempty (Subtype p)] (j : Subtype p) : Subtype p
参数：f : ι -> α；s : ι' -> Set ι；p : ι' -> Prop；Subtype p；Subtype p；j : Subtype p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an indexed family of sets `s j` over `j : Subtype p` and a function `f`, t
hen
`liminfReparam j` is equal to `j` if `f` is bounded below on `s j`, and otherwis
e to some
index `k` such that `f` is bounded below on `s k` (if there exists one).
To ensure good measurability behavior, this index `k` is chosen as the minimal s
uitable index.
This function is used to write down a liminf in a measurable way,
in `Filter.HasBasis.liminf_eq_ciSup_ciInf` and `Filter.HasBasis.liminf_eq_ite`.
-/
noncomputable def liminfReparam
    (f : ι → α) (s : ι' → Set ι) (p : ι' → Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) ↦ f i))}
  let g : ℕ → Subtype p := (exists_surjective_nat _).choose
  have Z : ∃ n, g n ∈ m ∨ ∀ j, j ∉ m := by
    by_cases! H : ∃ j, j ∈ m
    · rcases H with ⟨j, hj⟩
      rcases (exists_surjective_nat (Subtype p)).choose_spec j with ⟨n, rfl⟩
      exact ⟨n, Or.inl hj⟩
    · exact ⟨0, Or.inr H⟩
  if j ∈ m then j else g (Nat.find Z)

@[deprecated (since := "2026-07-18")]
alias liminf_reparam := liminfReparam

/-- Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of sets which are
not bounded below. -/
/-
**Filter.HasBasis.liminf_eq_ciSup_ciInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBas
is`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : ConditionallyCompl
eteLinearOrder α] {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι} [inst_1 : Co
untable (Subtype p)] [inst_2 : Nonempty (Subtype p)],   v.HasBasis p s →     ∀ {
f : ι → α},       (∀ (j : Subtype p), (s ↑j).Nonempty) →         (∃ j, BddBelow 
(Set.range fun i => f ↑i)) → Filter.liminf f v = ⨆ j, ⨅ i, f ↑i
参数：Subtype p；Subtype p；∀ (j : Subtype p), (s ↑j).Nonempty；∃ j, BddBelow (Set.ran
ge fun i => f ↑i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty
 ↑s
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.Iic_ciInf`：Set.Iic_ciInf [Nonempty ι] {f : ι -> α} (hf : BddBelow (r
ange f)) : Iic (⨅ i, f i) = ⋂ i, Iic (f i)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Filter.HasBasis.liminf_eq_sSup_iUnion_iInter`：∀ {α : Type u_1} [inst : C
onditionallyCompleteLattice α] {ι : Type u_6} {ι' : Type u_7} {f : ι → α} {v : F
ilter ι}   {p : ι' → Prop} {s : ι'…
· 使用引理 `sSup_iUnion_Iic`：sSup_iUnion_Iic (f : ι -> α) : sSup (⋃ (i : ι), Iic (f 
i)) = ⨆ i, f i

--- 原说明 ---
Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditio
nally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of
 sets which are
not bounded below.
-/
theorem HasBasis.liminf_eq_ciSup_ciInf {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι → α} (hs : ∀ (j : Subtype p), (s j).Nonempty)
    (H : ∃ (j : Subtype p), BddBelow (range (fun (i : s j) ↦ f i))) :
    liminf f v = ⨆ (j : Subtype p), ⨅ (i : s (liminfReparam f s p j)), f i := by
  classical
  rcases H with ⟨j0, hj0⟩
  let m : Set (Subtype p) := {j | BddBelow (range (fun (i : s j) ↦ f i))}
  have : ∀ (j : Subtype p), Nonempty (s j) := fun j ↦ Nonempty.coe_sort (hs j)
  have A : ⋃ (j : Subtype p), ⋂ (i : s j), Iic (f i) =
         ⋃ (j : Subtype p), ⋂ (i : s (liminfReparam f s p j)), Iic (f i) := by
    apply Subset.antisymm
    · apply iUnion_subset (fun j ↦ ?_)
      by_cases hj : j ∈ m
      · have : j = liminfReparam f s p j := by simp only [m, liminfReparam, hj, ite_true]
        conv_lhs => rw [this]
        apply subset_iUnion _ j
      · simp only [m, mem_ofPred_eq, ← nonempty_iInter_Iic_iff, not_nonempty_iff_eq_empty] at hj
        simp only [hj, empty_subset]
    · apply iUnion_subset (fun j ↦ ?_)
      exact subset_iUnion (fun (k : Subtype p) ↦ (⋂ (i : s k), Iic (f i))) (liminfReparam f s p j)
  have B : ∀ (j : Subtype p), ⋂ (i : s (liminfReparam f s p j)), Iic (f i) =
                                Iic (⨅ (i : s (liminfReparam f s p j)), f i) := by
    intro j
    apply (Iic_ciInf _).symm
    change liminfReparam f s p j ∈ m
    by_cases Hj : j ∈ m
    · simpa only [m, liminfReparam, if_pos Hj] using Hj
    · simp only [m, liminfReparam, if_neg Hj]
      have Z : ∃ n, (exists_surjective_nat (Subtype p)).choose n ∈ m ∨ ∀ j, j ∉ m := by
        rcases (exists_surjective_nat (Subtype p)).choose_spec j0 with ⟨n, rfl⟩
        exact ⟨n, Or.inl hj0⟩
      rcases Nat.find_spec Z with hZ | hZ
      · exact hZ
      · exact (hZ j0 hj0).elim
  simp_rw [hv.liminf_eq_sSup_iUnion_iInter, A, B, sSup_iUnion_Iic]

open scoped Classical in
/-- Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of sets which are
not bounded below. -/
/-
**Filter.HasBasis.liminf_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : ConditionallyCompl
eteLinearOrder α] {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι} [inst_1 : Co
untable (Subtype p)] [inst_2 : Nonempty (Subtype p)],   v.HasBasis p s →     ∀ (
f : ι → α),       Filter.liminf f v =         if ∃ j, s ↑j = ∅ then sSup Set.uni
v         else if ∀ (j : Subtype p), ¬BddBelow (Set.range fun i => f ↑i) then sS
up ∅ else ⨆ j, ⨅ i, f ↑i
参数：Subtype p；Subtype p；f : ι → α；j : Subtype p；Set.range fun i => f ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.HasBasis.liminf_eq_sSup_univ_of_empty`：∀ {α : Type u_1} {ι : Type
 u_4} {ι' : Type u_5} [inst : ConditionallyCompleteLattice α] {f : ι → α} {v : F
ilter ι}   {p : ι' → Prop} {s : ι'…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.HasBasis.liminf_eq_sSup_iUnion_iInter`：∀ {α : Type u_1} [inst : C
onditionallyCompleteLattice α] {ι : Type u_6} {ι' : Type u_7} {f : ι → α} {v : F
ilter ι}   {p : ι' → Prop} {s : ι'…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Filter.HasBasis.liminf_eq_ciSup_ciInf`：∀ {α : Type u_1} {ι : Type u_4} {
ι' : Type u_5} [inst : ConditionallyCompleteLinearOrder α] {v : Filter ι}   {p :
 ι' → Prop} {s : ι' → Set ι…
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)

--- 原说明 ---
Writing a liminf as a supremum of infimum, in a (possibly non-complete) conditio
nally complete
linear order. A reparametrization trick is needed to avoid taking the infimum of
 sets which are
not bounded below.
-/
theorem HasBasis.liminf_eq_ite {v : Filter ι} {p : ι' → Prop} {s : ι' → Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι → α) :
    liminf f v = if ∃ (j : Subtype p), s j = ∅ then sSup univ else
      if ∀ (j : Subtype p), ¬BddBelow (range (fun (i : s j) ↦ f i)) then sSup ∅
      else ⨆ (j : Subtype p), ⨅ (i : s (liminfReparam f s p j)), f i := by
  by_cases H : ∃ (j : Subtype p), s j = ∅
  · rw [if_pos H]
    rcases H with ⟨j, hj⟩
    simp [hv.liminf_eq_sSup_univ_of_empty j j.2 hj]
  rw [if_neg H]
  by_cases H' : ∀ (j : Subtype p), ¬BddBelow (range (fun (i : s j) ↦ f i))
  · have A : ∀ (j : Subtype p), ⋂ (i : s j), Iic (f i) = ∅ := by
      simp_rw [← not_nonempty_iff_eq_empty, nonempty_iInter_Iic_iff]
      exact H'
    simp_rw [if_pos H', hv.liminf_eq_sSup_iUnion_iInter, A, iUnion_empty]
  rw [if_neg H']
  apply hv.liminf_eq_ciSup_ciInf
  · push Not at H
    simpa only [nonempty_iff_ne_empty] using H
  · push Not at H'
    exact H'

/-- Given an indexed family of sets `s j` and a function `f`, then `limsupReparam j` is equal
to `j` if `f` is bounded above on `s j`, and otherwise to some index `k` such that `f` is bounded
above on `s k` (if there exists one). To ensure good measurability behavior, this index `k` is
chosen as the minimal suitable index. This function is used to write down a limsup in a measurable
way, in `Filter.HasBasis.limsup_eq_ciInf_ciSup` and `Filter.HasBasis.limsup_eq_ite`. -/
/-
**Filter.limsupReparam** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：limsupReparam (f : ι -> α) (s : ι' -> Set ι) (p : ι' -> Prop) [Countable (
Subtype p)] [Nonempty (Subtype p)] (j : Subtype p) : Subtype p
参数：f : ι -> α；s : ι' -> Set ι；p : ι' -> Prop；Subtype p；Subtype p；j : Subtype p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an indexed family of sets `s j` and a function `f`, then `limsupReparam j`
 is equal
to `j` if `f` is bounded above on `s j`, and otherwise to some index `k` such th
at `f` is bounded
above on `s k` (if there exists one). To ensure good measurability behavior, thi
s index `k` is
chosen as the minimal suitable index. This function is used to write down a lims
up in a measurable
way, in `Filter.HasBasis.limsup_eq_ciInf_ciSup` and `Filter.HasBasis.limsup_eq_i
te`.
-/
noncomputable def limsupReparam
    (f : ι → α) (s : ι' → Set ι) (p : ι' → Prop) [Countable (Subtype p)] [Nonempty (Subtype p)]
    (j : Subtype p) : Subtype p :=
  liminfReparam (α := αᵒᵈ) f s p j

@[deprecated (since := "2026-07-18")]
alias limsup_reparam := limsupReparam

/-- Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the supremum of sets which are
not bounded above. -/
/-
**Filter.HasBasis.limsup_eq_ciInf_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBas
is`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : ConditionallyCompl
eteLinearOrder α] {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι} [inst_1 : Co
untable (Subtype p)] [inst_2 : Nonempty (Subtype p)],   v.HasBasis p s →     ∀ {
f : ι → α},       (∀ (j : Subtype p), (s ↑j).Nonempty) →         (∃ j, BddAbove 
(Set.range fun i => f ↑i)) → Filter.limsup f v = ⨅ j, ⨆ i, f ↑i
参数：Subtype p；Subtype p；∀ (j : Subtype p), (s ↑j).Nonempty；∃ j, BddAbove (Set.ran
ge fun i => f ↑i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.liminf_eq_ciSup_ciInf`：∀ {α : Type u_1} {ι : Type u_4} {
ι' : Type u_5} [inst : ConditionallyCompleteLinearOrder α] {v : Filter ι}   {p :
 ι' → Prop} {s : ι' → Set ι…

--- 原说明 ---
Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditi
onally complete
linear order. A reparametrization trick is needed to avoid taking the supremum o
f sets which are
not bounded above.
-/
theorem HasBasis.limsup_eq_ciInf_ciSup {v : Filter ι}
    {p : ι' → Prop} {s : ι' → Set ι} [Countable (Subtype p)] [Nonempty (Subtype p)]
    (hv : v.HasBasis p s) {f : ι → α} (hs : ∀ (j : Subtype p), (s j).Nonempty)
    (H : ∃ (j : Subtype p), BddAbove (range (fun (i : s j) ↦ f i))) :
    limsup f v = ⨅ (j : Subtype p), ⨆ (i : s (limsupReparam f s p j)), f i :=
  HasBasis.liminf_eq_ciSup_ciInf (α := αᵒᵈ) hv hs H

open scoped Classical in
/-- Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditionally complete
linear order. A reparametrization trick is needed to avoid taking the supremum of sets which are
not bounded below. -/
/-
**Filter.HasBasis.limsup_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} {ι' : Type u_5} [inst : ConditionallyCompl
eteLinearOrder α] {v : Filter ι}   {p : ι' → Prop} {s : ι' → Set ι} [inst_1 : Co
untable (Subtype p)] [inst_2 : Nonempty (Subtype p)],   v.HasBasis p s →     ∀ (
f : ι → α),       Filter.limsup f v =         if ∃ j, s ↑j = ∅ then sInf Set.uni
v         else if ∀ (j : Subtype p), ¬BddAbove (Set.range fun i => f ↑i) then sI
nf ∅ else ⨅ j, ⨆ i, f ↑i
参数：Subtype p；Subtype p；f : ι → α；j : Subtype p；Set.range fun i => f ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.liminf_eq_ite`：∀ {α : Type u_1} {ι : Type u_4} {ι' : Typ
e u_5} [inst : ConditionallyCompleteLinearOrder α] {v : Filter ι}   {p : ι' → Pr
op} {s : ι' → Set ι…

--- 原说明 ---
Writing a limsup as an infimum of supremum, in a (possibly non-complete) conditi
onally complete
linear order. A reparametrization trick is needed to avoid taking the supremum o
f sets which are
not bounded below.
-/
theorem HasBasis.limsup_eq_ite {v : Filter ι} {p : ι' → Prop} {s : ι' → Set ι}
    [Countable (Subtype p)] [Nonempty (Subtype p)] (hv : v.HasBasis p s) (f : ι → α) :
    limsup f v = if ∃ (j : Subtype p), s j = ∅ then sInf univ else
      if ∀ (j : Subtype p), ¬BddAbove (range (fun (i : s j) ↦ f i)) then sInf ∅
      else ⨅ (j : Subtype p), ⨆ (i : s (limsupReparam f s p j)), f i :=
  HasBasis.liminf_eq_ite (α := αᵒᵈ) hv f

end Classical

end ConditionallyCompleteLinearOrder

end Filter

section Order

/-
**GaloisConnection.l_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β] [Conditional
lyCompleteLattice γ] {f : Filter α} {v : α -> β} {l : β -> γ} {u : γ -> β} (gc :
 GaloisConnection l u) (hlv : f.IsBoundedUnder (· <= ·) fun x => l (v x)
参数：gc : GaloisConnection l u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_limsSup_of_le`：le_limsSup_of_le {f : Filter α} {a} (hf : f.IsB
ounded (· <= ·)
· 使用定理 `Filter.limsSup_le_of_le`：limsSup_le_of_le {f : Filter α} {a} (hf : f.IsC
obounded (· <= ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β]
    [ConditionallyCompleteLattice γ] {f : Filter α} {v : α → β} {l : β → γ} {u : γ → β}
    (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· ≤ ·) fun x => l (v x) := by isBoundedDefault)
    (hv_co : f.IsCoboundedUnder (· ≤ ·) v := by isBoundedDefault) :
    l (limsup v f) ≤ limsup (fun x => l (v x)) f := by
  refine le_limsSup_of_le hlv fun c hc => ?_
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc ⊢
  exact limsSup_le_of_le hv_co hc
/-
**OrderIso.limsup_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyC
ompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o γ) (hu : f.IsBoundedUnde
r (· <= ·) u
参数：g : β ≃o γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.l_limsup_le`：GaloisConnection.l_limsup_le [Conditionall
yCompleteLattice β] [ConditionallyCompleteLattice γ] {f : Filter α} {v : α -> β}
 {l : β -> γ} {u :…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· ≤ ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· ≤ ·) fun x => g (u x) := by isBoundedDefault) :
    g (limsup u f) = limsup (fun x => g (u x)) f := by
  refine le_antisymm ((OrderIso.to_galoisConnection g).l_limsup_le hgu hu_co) ?_
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f, g.symm_symm]
  refine g.monotone ?_
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 2 [hf]
  refine (OrderIso.to_galoisConnection g.symm).l_limsup_le ?_ hgu_co
  simp_rw [g.symm_apply_apply]
  exact hu
/-
**OrderIso.liminf_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyC
ompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o γ) (hu : f.IsBoundedUnde
r (· >= ·) u
参数：g : β ≃o γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.limsup_apply`：OrderIso.limsup_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
-/
theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hu_co : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (hgu : f.IsBoundedUnder (· ≥ ·) fun x => g (u x) := by isBoundedDefault)
    (hgu_co : f.IsCoboundedUnder (· ≥ ·) fun x => g (u x) := by isBoundedDefault) :
    g (liminf u f) = liminf (fun x => g (u x)) f :=
  OrderIso.limsup_apply (β := βᵒᵈ) (γ := γᵒᵈ) g.dual hu hu_co hgu hgu_co

end Order

section MinMax

open Filter

/-
**limsup_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsup_max [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α ->
 β} (h₁ : f.IsCoboundedUnder (· <= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.sup`：∀ {α : Type u_1} {β : Type u_2} [inst : Semil
atticeSup α] {f : Filter β} {u v : β → α},   Filter.IsBoundedUnder (fun x1 x2 =>
 x1 ≤ x2) f u →…
· 使用定理 `isCoboundedUnder_le_max`：isCoboundedUnder_le_max [LinearOrder β] {f : Fi
lter α} {u v : α -> β} (h : f.IsCoboundedUnder (· <= ·) u ∨ f.IsCoboundedUnder (
· <= ·) v) : …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem limsup_max [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α → β}
    (h₁ : f.IsCoboundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₂ : f.IsCoboundedUnder (· ≤ ·) v := by isBoundedDefault)
    (h₃ : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h₄ : f.IsBoundedUnder (· ≤ ·) v := by isBoundedDefault) :
    limsup (fun a ↦ max (u a) (v a)) f = max (limsup u f) (limsup v f) := by
  have bddmax := IsBoundedUnder.sup h₃ h₄
  have cobddmax := isCoboundedUnder_le_max (v := v) (Or.inl h₁)
  apply le_antisymm
  · refine (limsup_le_iff cobddmax bddmax).2 (fun b hb ↦ ?_)
    have hu := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb) h₃
    have hv := eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_right _ _) hb) h₄
    refine mem_of_superset (inter_mem hu hv) (fun _ ↦ by simp)
  · exact max_le (c := limsup (fun a ↦ max (u a) (v a)) f)
      (limsup_le_limsup (Eventually.of_forall (fun a : α ↦ le_max_left (u a) (v a))) h₁ bddmax)
      (limsup_le_limsup (Eventually.of_forall (fun a : α ↦ le_max_right (u a) (v a))) h₂ bddmax)
/-
**liminf_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liminf_min [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α ->
 β} (h₁ : f.IsCoboundedUnder (· >= ·) u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsup_max`：limsup_max [ConditionallyCompleteLinearOrder β] {f : Filter 
α} {u v : α -> β} (h₁ : f.IsCoboundedUnder (· <= ·) u
-/
theorem liminf_min [ConditionallyCompleteLinearOrder β] {f : Filter α} {u v : α → β}
    (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₂ : f.IsCoboundedUnder (· ≥ ·) v := by isBoundedDefault)
    (h₃ : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h₄ : f.IsBoundedUnder (· ≥ ·) v := by isBoundedDefault) :
    liminf (fun a ↦ min (u a) (v a)) f = min (liminf u f) (liminf v f) :=
  limsup_max (β := βᵒᵈ) h₁ h₂ h₃ h₄

open Finset
/-
**limsup_finset_sup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsup_finset_sup' [ConditionallyCompleteLinearOrder β] {f : Filter α} {F 
: ι -> α -> β} {s : Finset ι} (hs : s.Nonempty) (h₁ : forall i in s, f.IsCobound
edUnder (· <= ·) (F i)
参数：hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `isBoundedUnder_le_finset_sup'`：isBoundedUnder_le_finset_sup' [LinearOrde
r β] [Nonempty β] {f : Filter α} {F : ι -> α -> β} {s : Finset ι} (hs : s.Nonemp
ty) (h : forall i i…
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `isCoboundedUnder_le_finset_sup'`：isCoboundedUnder_le_finset_sup' [Linear
Order β] {f : Filter α} {F : ι -> α -> β} {s : Finset ι} (hs : s.Nonempty) (h : 
exists i in s, f.IsCo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem limsup_finset_sup' [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι} (hs : s.Nonempty)
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    limsup (fun a ↦ sup' s hs (fun i ↦ F i a)) f = sup' s hs (fun i ↦ limsup (F i) f) := by
  have bddsup := isBoundedUnder_le_finset_sup' hs h₂
  apply le_antisymm
  · have h₃ : ∃ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by
      rcases hs with ⟨i, i_s⟩
      use i, i_s
      exact h₁ i i_s
    have cobddsup := isCoboundedUnder_le_finset_sup' hs h₃
    refine (limsup_le_iff cobddsup bddsup).2 (fun b hb ↦ ?_)
    simp only [gt_iff_lt, sup'_lt_iff, eventually_all_finset] at hb ⊢
    exact fun i i_s ↦ eventually_lt_of_limsup_lt (hb i i_s) (h₂ i i_s)
  · apply Finset.sup'_le hs (fun i ↦ limsup (F i) f)
    refine fun i i_s ↦ limsup_le_limsup (Eventually.of_forall (fun a ↦ ?_)) (h₁ i i_s) bddsup
    simp only [le_sup'_iff]
    use i, i_s
/-
**limsup_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limsup_finset_sup [ConditionallyCompleteLinearOrder β] [OrderBot β] {f : F
ilter α} {F : ι -> α -> β} {s : Finset ι} (h₁ : forall i in s, f.IsCoboundedUnde
r (· <= ·) (F i)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
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
· 使用定理 `csInf_univ`：csInf_univ [ConditionallyCompleteLattice α] [OrderBot α] : s
Inf (univ : Set α) = ⊥
· 使用定理 `Finset.sup_bot`：sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `limsup_finset_sup'`：limsup_finset_sup' [ConditionallyCompleteLinearOrder
 β] {f : Filter α} {F : ι -> α -> β} {s : Finset ι} (hs : s.Nonempty) (h₁ : fora
ll i in …
-/
theorem limsup_finset_sup [ConditionallyCompleteLinearOrder β] [OrderBot β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι}
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    limsup (fun a ↦ sup s (fun i ↦ F i a)) f = sup s (fun i ↦ limsup (F i) f) := by
  rcases eq_or_neBot f with (rfl | _)
  · simp [limsup_eq, csInf_univ]
  rcases Finset.eq_empty_or_nonempty s with (rfl | s_nemp)
  · simp only [sup_empty, limsup_const]
  rw [← Finset.sup'_eq_sup s_nemp fun i ↦ limsup (F i) f, ← limsup_finset_sup' s_nemp h₁ h₂]
  congr
  ext a
  exact Eq.symm (Finset.sup'_eq_sup s_nemp (fun i ↦ F i a))
/-
**liminf_finset_inf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liminf_finset_inf' [ConditionallyCompleteLinearOrder β] {f : Filter α} {F 
: ι -> α -> β} {s : Finset ι} (hs : s.Nonempty) (h₁ : forall i in s, f.IsCobound
edUnder (· >= ·) (F i)
参数：hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsup_finset_sup'`：limsup_finset_sup' [ConditionallyCompleteLinearOrder
 β] {f : Filter α} {F : ι -> α -> β} {s : Finset ι} (hs : s.Nonempty) (h₁ : fora
ll i in …
-/
theorem liminf_finset_inf' [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι} (hs : s.Nonempty)
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    liminf (fun a ↦ inf' s hs (fun i ↦ F i a)) f = inf' s hs (fun i ↦ liminf (F i) f) :=
  limsup_finset_sup' (β := βᵒᵈ) hs h₁ h₂
/-
**liminf_finset_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：liminf_finset_inf [ConditionallyCompleteLinearOrder β] [OrderTop β] {f : F
ilter α} {F : ι -> α -> β} {s : Finset ι} (h₁ : forall i in s, f.IsCoboundedUnde
r (· >= ·) (F i)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `limsup_finset_sup`：limsup_finset_sup [ConditionallyCompleteLinearOrder β
] [OrderBot β] {f : Filter α} {F : ι -> α -> β} {s : Finset ι} (h₁ : forall i in
 s, f.I…
-/
theorem liminf_finset_inf [ConditionallyCompleteLinearOrder β] [OrderTop β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι}
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≥ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    liminf (fun a ↦ inf s (fun i ↦ F i a)) f = inf s (fun i ↦ liminf (F i) f) :=
  limsup_finset_sup (β := βᵒᵈ) h₁ h₂

end MinMax

