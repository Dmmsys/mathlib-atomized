/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Finsupp

/-!
# Locus of unequal values of finitely supported functions

Let `α N` be two Types, assume that `N` has a `0` and let `f g : α →₀ N` be finitely supported
functions.

## Main definition

* `Finsupp.neLocus f g : Finset α`, the finite subset of `α` where `f` and `g` differ.

In the case in which `N` is an additive group, `Finsupp.neLocus f g` coincides with
`Finsupp.support (f - g)`.
-/

@[expose] public section


variable {α M N P : Type*}

namespace Finsupp

variable [DecidableEq α]

section NHasZero

variable [DecidableEq N] [Zero N] (f g : α →₀ N)

/-- Given two finitely supported functions `f g : α →₀ N`, `Finsupp.neLocus f g` is the `Finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
/-
**Finsupp.neLocus** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：neLocus (f g : α ->₀ N) : Finset α
参数：f g : α ->₀ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two finitely supported functions `f g : α →₀ N`, `Finsupp.neLocus f g` is 
the `Finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations witho
ut subtraction.
-/
def neLocus (f g : α →₀ N) : Finset α :=
  (f.support ∪ g.support).filter fun x => f x ≠ g x

@[simp]
/-
**Finsupp.mem_neLocus** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_neLocus {f g : α ->₀ N} {a : α} : a in f.neLocus g ↔ f a != g a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ne.ne_or_ne`：Ne.ne_or_ne {x y : α} (z : α) (h : x != y) : x != z ∨ y != 
z
-/
theorem mem_neLocus {f g : α →₀ N} {a : α} : a ∈ f.neLocus g ↔ f a ≠ g a := by
  simpa only [neLocus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _
/-
**Finsupp.notMem_neLocus** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：notMem_neLocus {f g : α ->₀ N} {a : α} : a ∉ f.neLocus g ↔ f a = g a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finsupp.mem_neLocus`：mem_neLocus {f g : α ->₀ N} {a : α} : a in f.neLocu
s g ↔ f a != g a
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
-/
theorem notMem_neLocus {f g : α →₀ N} {a : α} : a ∉ f.neLocus g ↔ f a = g a :=
  mem_neLocus.not.trans not_ne_iff

@[simp]
/-
**Finsupp.coe_neLocus** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_neLocus : ↑(f.neLocus g) = { x | f x != g x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finsupp.mem_neLocus`：mem_neLocus {f g : α ->₀ N} {a : α} : a in f.neLocu
s g ↔ f a != g a
-/
theorem coe_neLocus : ↑(f.neLocus g) = { x | f x ≠ g x } := by
  ext
  exact mem_neLocus

@[simp]
/-
**Finsupp.neLocus_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_eq_empty {f g : α ->₀ N} : f.neLocus g = ∅ ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finsupp.mem_neLocus`：mem_neLocus {f g : α ->₀ N} {a : α} : a in f.neLocu
s g ↔ f a != g a
· 使用定理 `Finset.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Finse
t α} : s = ∅ ↔ forall x, x ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
-/
theorem neLocus_eq_empty {f g : α →₀ N} : f.neLocus g = ∅ ↔ f = g :=
  ⟨fun h =>
    ext fun a => not_not.mp (mem_neLocus.not.mp (Finset.eq_empty_iff_forall_notMem.mp h a)),
    fun h => h ▸ by simp only [neLocus, Ne, not_true, Finset.filter_false]⟩

@[simp]
/-
**Finsupp.nonempty_neLocus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：nonempty_neLocus_iff {f g : α ->₀ N} : (f.neLocus g).Nonempty ↔ f != g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finsupp.neLocus_eq_empty`：neLocus_eq_empty {f g : α ->₀ N} : f.neLocus g
 = ∅ ↔ f = g
-/
theorem nonempty_neLocus_iff {f g : α →₀ N} : (f.neLocus g).Nonempty ↔ f ≠ g :=
  Finset.nonempty_iff_ne_empty.trans neLocus_eq_empty.not
/-
**Finsupp.neLocus_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_comm : f.neLocus g = g.neLocus f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neLocus_comm : f.neLocus g = g.neLocus f := by
  simp_rw [neLocus, Finset.union_comm, ne_comm]

@[simp]
/-
**Finsupp.neLocus_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_zero_right : f.neLocus 0 = f.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_neLocus`：mem_neLocus {f g : α ->₀ N} {a : α} : a in f.neLocu
s g ↔ f a != g a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neLocus_zero_right : f.neLocus 0 = f.support := by
  ext
  rw [mem_neLocus, mem_support_iff, coe_zero, Pi.zero_apply]

@[simp]
/-
**Finsupp.neLocus_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_zero_left : (0 : α ->₀ N).neLocus f = f.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.neLocus_comm`：neLocus_comm : f.neLocus g = g.neLocus f
· 使用定理 `Finsupp.neLocus_zero_right`：neLocus_zero_right : f.neLocus 0 = f.support
-/
theorem neLocus_zero_left : (0 : α →₀ N).neLocus f = f.support :=
  (neLocus_comm _ _).trans (neLocus_zero_right _)

end NHasZero

section NeLocusAndMaps

/-
**Finsupp.subset_mapRange_neLocus** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subset_mapRange_neLocus [DecidableEq N] [Zero N] [DecidableEq M] [Zero M] 
(f g : α ->₀ N) {F : N -> M} (F0 : F 0 = 0) : (f.mapRange F F0).neLocus (g.mapRa
nge F F0) subseteq f.neLocus g
参数：f g : α ->₀ N；F0 : F 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem subset_mapRange_neLocus [DecidableEq N] [Zero N] [DecidableEq M] [Zero M] (f g : α →₀ N)
    {F : N → M} (F0 : F 0 = 0) : (f.mapRange F F0).neLocus (g.mapRange F F0) ⊆ f.neLocus g :=
  fun x => by simpa only [mem_neLocus, mapRange_apply, not_imp_not] using congr_arg F
/-
**Finsupp.zipWith_neLocus_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zipWith_neLocus_eq_left [DecidableEq N] [Zero M] [DecidableEq P] [Zero P] 
[Zero N] {F : M -> N -> P} (F0 : F 0 0 = 0) (f : α ->₀ M) (g₁ g₂ : α ->₀ N) (hF 
: forall f, Function.Injective fun g => F f g) : (zipWith F F0 f g₁).neLocus (zi
pWith F F0 f g₂) = g₁.neLocus g₂
参数：F0 : F 0 0 = 0；f : α ->₀ M；g₁ g₂ : α ->₀ N；hF : forall f, Function.Injective 
fun g => F f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
-/
theorem zipWith_neLocus_eq_left [DecidableEq N] [Zero M] [DecidableEq P] [Zero P] [Zero N]
    {F : M → N → P} (F0 : F 0 0 = 0) (f : α →₀ M) (g₁ g₂ : α →₀ N)
    (hF : ∀ f, Function.Injective fun g => F f g) :
    (zipWith F F0 f g₁).neLocus (zipWith F F0 f g₂) = g₁.neLocus g₂ := by
  ext
  simpa only [mem_neLocus] using! (hF _).ne_iff
/-
**Finsupp.zipWith_neLocus_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zipWith_neLocus_eq_right [DecidableEq M] [Zero M] [DecidableEq P] [Zero P]
 [Zero N] {F : M -> N -> P} (F0 : F 0 0 = 0) (f₁ f₂ : α ->₀ M) (g : α ->₀ N) (hF
 : forall g, Function.Injective fun f => F f g) : (zipWith F F0 f₁ g).neLocus (z
ipWith F F0 f₂ g) = f₁.neLocus f₂
参数：F0 : F 0 0 = 0；f₁ f₂ : α ->₀ M；g : α ->₀ N；hF : forall g, Function.Injective 
fun f => F f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
-/
theorem zipWith_neLocus_eq_right [DecidableEq M] [Zero M] [DecidableEq P] [Zero P] [Zero N]
    {F : M → N → P} (F0 : F 0 0 = 0) (f₁ f₂ : α →₀ M) (g : α →₀ N)
    (hF : ∀ g, Function.Injective fun f => F f g) :
    (zipWith F F0 f₁ g).neLocus (zipWith F F0 f₂ g) = f₁.neLocus f₂ := by
  ext
  simpa only [mem_neLocus] using! (hF _).ne_iff
/-
**Finsupp.mapRange_neLocus_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_neLocus_eq [DecidableEq N] [DecidableEq M] [Zero M] [Zero N] (f g
 : α ->₀ N) {F : N -> M} (F0 : F 0 = 0) (hF : Function.Injective F) : (f.mapRang
e F F0).neLocus (g.mapRange F F0) = f.neLocus g
参数：f g : α ->₀ N；F0 : F 0 = 0；hF : Function.Injective F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
-/
theorem mapRange_neLocus_eq [DecidableEq N] [DecidableEq M] [Zero M] [Zero N] (f g : α →₀ N)
    {F : N → M} (F0 : F 0 = 0) (hF : Function.Injective F) :
    (f.mapRange F F0).neLocus (g.mapRange F F0) = f.neLocus g := by
  ext
  simpa only [mem_neLocus] using! hF.ne_iff

end NeLocusAndMaps

variable [DecidableEq N]

@[simp]
/-
**Finsupp.neLocus_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_add_left [AddLeftCancelMonoid N] (f g h : α ->₀ N) : (f + g).neLoc
us (f + h) = g.neLocus h
参数：f g h : α ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.zipWith_neLocus_eq_left`：zipWith_neLocus_eq_left [DecidableEq N]
 [Zero M] [DecidableEq P] [Zero P] [Zero N] {F : M -> N -> P} (F0 : F 0 0 = 0) (
f : α ->₀ M) (g₁ g₂ :…
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem neLocus_add_left [AddLeftCancelMonoid N] (f g h : α →₀ N) :
    (f + g).neLocus (f + h) = g.neLocus h :=
  zipWith_neLocus_eq_left _ _ _ _ add_right_injective

@[simp]
/-
**Finsupp.neLocus_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_add_right [AddRightCancelMonoid N] (f g h : α ->₀ N) : (f + h).neL
ocus (g + h) = f.neLocus g
参数：f g h : α ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.zipWith_neLocus_eq_right`：zipWith_neLocus_eq_right [DecidableEq 
M] [Zero M] [DecidableEq P] [Zero P] [Zero N] {F : M -> N -> P} (F0 : F 0 0 = 0)
 (f₁ f₂ : α ->₀ M) (g …
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem neLocus_add_right [AddRightCancelMonoid N] (f g h : α →₀ N) :
    (f + h).neLocus (g + h) = f.neLocus g :=
  zipWith_neLocus_eq_right _ _ _ _ add_left_injective

section AddGroup

variable [AddGroup N] (f f₁ f₂ g g₁ g₂ : α →₀ N)

@[simp]
/-
**Finsupp.neLocus_neg_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_neg_neg : neLocus (-f) (-g) = f.neLocus g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapRange_neLocus_eq`：mapRange_neLocus_eq [DecidableEq N] [Decida
bleEq M] [Zero M] [Zero N] (f g : α ->₀ N) {F : N -> M} (F0 : F 0 = 0) (hF : Fun
ction.Injective F…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
theorem neLocus_neg_neg : neLocus (-f) (-g) = f.neLocus g :=
  mapRange_neLocus_eq _ _ neg_zero neg_injective
/-
**Finsupp.neLocus_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_neg : neLocus (-f) g = f.neLocus (-g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.neLocus_neg_neg`：neLocus_neg_neg : neLocus (-f) (-g) = f.neLocus
 g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neLocus_neg : neLocus (-f) g = f.neLocus (-g) := by rw [← neLocus_neg_neg, neg_neg]
/-
**Finsupp.neLocus_eq_support_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_eq_support_sub : f.neLocus g = (f - g).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.neLocus_add_right`：neLocus_add_right [AddRightCancelMonoid N] (f
 g h : α ->₀ N) : (f + h).neLocus (g + h) = f.neLocus g
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Finsupp.neLocus_zero_right`：neLocus_zero_right : f.neLocus 0 = f.support
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem neLocus_eq_support_sub : f.neLocus g = (f - g).support := by
  rw [← neLocus_add_right _ _ (-g), add_neg_cancel, neLocus_zero_right, sub_eq_add_neg]

@[simp]
/-
**Finsupp.neLocus_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_sub_left : neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.neLocus.congr_simp`：∀ {α : Type u_1} {N : Type u_3} [inst : Deci
dableEq α] {inst_1 : DecidableEq N} [inst_2 : DecidableEq N]   [inst_3 : Zero N]
 (f f_1 : α →₀ N…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Finsupp.neLocus_add_left`：neLocus_add_left [AddLeftCancelMonoid N] (f g 
h : α ->₀ N) : (f + g).neLocus (f + h) = g.neLocus h
· 使用定理 `Finsupp.neLocus_neg_neg`：neLocus_neg_neg : neLocus (-f) (-g) = f.neLocus
 g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neLocus_sub_left : neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂ := by
  simp only [sub_eq_add_neg, neLocus_add_left, neLocus_neg_neg]

@[simp]
/-
**Finsupp.neLocus_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_sub_right : neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.neLocus.congr_simp`：∀ {α : Type u_1} {N : Type u_3} [inst : Deci
dableEq α] {inst_1 : DecidableEq N} [inst_2 : DecidableEq N]   [inst_3 : Zero N]
 (f f_1 : α →₀ N…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Finsupp.neLocus_add_right`：neLocus_add_right [AddRightCancelMonoid N] (f
 g h : α ->₀ N) : (f + h).neLocus (g + h) = f.neLocus g
-/
theorem neLocus_sub_right : neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂ := by
  simpa only [sub_eq_add_neg] using neLocus_add_right _ _ _

@[simp]
/-
**Finsupp.neLocus_self_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_self_add_right : neLocus f (f + g) = g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.neLocus_zero_left`：neLocus_zero_left : (0 : α ->₀ N).neLocus f =
 f.support
· 使用定理 `Finsupp.neLocus_add_left`：neLocus_add_left [AddLeftCancelMonoid N] (f g 
h : α ->₀ N) : (f + g).neLocus (f + h) = g.neLocus h
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem neLocus_self_add_right : neLocus f (f + g) = g.support := by
  rw [← neLocus_zero_left, ← neLocus_add_left f 0 g, add_zero]

@[simp]
/-
**Finsupp.neLocus_self_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_self_add_left : neLocus (f + g) f = g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.neLocus_comm`：neLocus_comm : f.neLocus g = g.neLocus f
· 使用定理 `Finsupp.neLocus_self_add_right`：neLocus_self_add_right : neLocus f (f + 
g) = g.support
-/
theorem neLocus_self_add_left : neLocus (f + g) f = g.support := by
  rw [neLocus_comm, neLocus_self_add_right]

@[simp]
/-
**Finsupp.neLocus_self_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_self_sub_right : neLocus f (f - g) = g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Finsupp.neLocus_self_add_right`：neLocus_self_add_right : neLocus f (f + 
g) = g.support
· 使用引理 `Finsupp.support_neg`：support_neg (f : ι ->₀ G) : support (-f) = support 
f
-/
theorem neLocus_self_sub_right : neLocus f (f - g) = g.support := by
  rw [sub_eq_add_neg, neLocus_self_add_right, support_neg]

@[simp]
/-
**Finsupp.neLocus_self_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：neLocus_self_sub_left : neLocus (f - g) f = g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.neLocus_comm`：neLocus_comm : f.neLocus g = g.neLocus f
· 使用定理 `Finsupp.neLocus_self_sub_right`：neLocus_self_sub_right : neLocus f (f - 
g) = g.support
-/
theorem neLocus_self_sub_left : neLocus (f - g) f = g.support := by
  rw [neLocus_comm, neLocus_self_sub_right]

end AddGroup

end Finsupp

