/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity.Basic

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

## Main definitions

* `Convexity.StdSimplex R M`: A finitely supported probability distribution over elements of `M`
  with coefficients in `R`. The weights are non-negative and sum to 1.
* `Convexity.StdSimplex.map`: Map a function over the support of a standard simplex.
* `Convexity.ConvexSpace R M`: A typeclass for spaces `M` equipped with an operation
  `Convexity.sConvexComb : StdSimplex R M → M` satisfying monadic laws.
* `Convexity.iConvexComb`: Indexed convex combination operator.
* `Convexity.convexCombPair`: Binary convex combinations of two points.

## Design

The design follows a monadic structure where `StdSimplex R` forms a monad and `convexCombination`
is a monadic algebra. This eliminates the need for explicit extensionality axioms and resolves
universe issues with indexed families.

-/

@[expose] public noncomputable section

universe u v w u₁ u₂

open Finsupp

namespace Convexity
variable {R X M N P I J K : Type*}

/--
A finitely supported probability distribution over elements of `M` with coefficients in `R`.
The weights are non-negative and sum to 1.
-/
/-
**Convexity.StdSimplex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Convexity`。
形式化陈述：(R : Type u) → [LE R] → [AddCommMonoid R] → [One R] → Type v → Type (max u
 v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finitely supported probability distribution over elements of `M` with coeffici
ents in `R`.
The weights are non-negative and sum to 1.
-/
structure StdSimplex (R : Type u) [LE R] [AddCommMonoid R] [One R] (M : Type v) where
  /-- The weights of the `StdSimplex` as a `Finsupp`. -/
  weights : M →₀ R
  /-- All weights are non-negative. -/
  nonneg : 0 ≤ weights
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] StdSimplex.total
grind_pattern StdSimplex.nonneg => self.weights
grind_pattern StdSimplex.total => self.weights

initialize_simps_projections StdSimplex (as_prefix weights)

namespace StdSimplex
section Semiring
variable {R : Type u} [PartialOrder R] [Semiring R] {M N P : Type*} {w : StdSimplex R M} {x : M}

/-
**Convexity.StdSimplex.weights_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.StdSi
mplex`。
形式化陈述：∀ {R : Type u} [inst : PartialOrder R] [inst_1 : Semiring R] {M : Type u_9
} {w : Convexity.StdSimplex R M} (i : M),   0 ≤ w.weights i
参数：i : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.nonneg`：∀ {R : Type u} [inst : LE R] [inst_1 : AddC
ommMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   
0 ≤ self.weights
-/
@[simp] lemma weights_nonneg {w : StdSimplex R M} (i : M) : 0 ≤ w.weights i := w.nonneg i
/-
**Convexity.StdSimplex.weights_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.StdS
implex`。
形式化陈述：∀ {R : Type u} [inst : PartialOrder R] [inst_1 : Semiring R] {M : Type u_9
} [Nontrivial R]   (w : Convexity.StdSimplex R M), w.weights ≠ 0
参数：w : Convexity.StdSimplex R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma weights_ne_zero [Nontrivial R] : ∀ w : StdSimplex R M, w.weights ≠ 0 := by
  rintro ⟨_, -, total⟩ rfl; simp at total
/-
**Convexity.StdSimplex.support_weights_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Conve
xity.StdSimplex`。
形式化陈述：support_weights_nonempty [Nontrivial R] (w : StdSimplex R M) : w.weights.s
upport.Nonempty
参数：w : StdSimplex R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma support_weights_nonempty [Nontrivial R] (w : StdSimplex R M) :
    w.weights.support.Nonempty := by simp
/-
**Convexity.StdSimplex.nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex`
。
形式化陈述：nonempty [Nontrivial R] (w : StdSimplex R M) : Nonempty M
参数：w : StdSimplex R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.to_type`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → N
onempty α
· 使用引理 `Convexity.StdSimplex.support_weights_nonempty`：support_weights_nonempty 
[Nontrivial R] (w : StdSimplex R M) : w.weights.support.Nonempty
-/
lemma nonempty [Nontrivial R] (w : StdSimplex R M) : Nonempty M :=
  w.support_weights_nonempty.to_type
/-
**Convexity.StdSimplex.weights_inj** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.StdSimpl
ex`。
形式化陈述：∀ {R : Type u} [inst : PartialOrder R] [inst_1 : Semiring R] {M : Type u_9
} {f g : Convexity.StdSimplex R M},   f.weights = g.weights ↔ f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.mk.injEq`：∀ {R : Type u} [inst : LE R] [inst_1 : Ad
dCommMonoid R] [inst_2 : One R] {M : Type v} (weights : M →₀ R)   (nonneg : 0 ≤ 
weights) (total : (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma weights_inj {f g : StdSimplex R M} : f.weights = g.weights ↔ f = g := by
  cases f; cases g; simp

@[ext] alias ⟨ext, _⟩ := weights_inj

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
@[simps weights]
/-
**Convexity.StdSimplex.single** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：single (x : M) : StdSimplex R M where weights
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point mass distribution concentrated at `x`.
-/
def single (x : M) : StdSimplex R M where
  weights := .single x 1
  nonneg := by simp
  total := by simp
/-
**Convexity.StdSimplex.mk_single** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.StdSimplex
`。
形式化陈述：mk_single (x : M) {nonneg total} : (mk (.single x (1 : R)) nonneg total) =
 single x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_single (x : M) {nonneg total} : (mk (.single x (1 : R)) nonneg total) = single x := rfl
/-
**Convexity.StdSimplex.support_weights_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `C
onvexity.StdSimplex`。
形式化陈述：∀ {R : Type u} [inst : PartialOrder R] [inst_1 : Semiring R] {M : Type u_9
} {w : Convexity.StdSimplex R M} {x : M}   [inst_2 : IsStrictOrderedRing R], w.w
eights.support = {x} ↔ w = Convexity.StdSimplex.single x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_eq_singleton'`：support_eq_singleton' {f : α ->₀ M} {a : 
α} : f.support = {a} ↔ exists b != 0, f = single a b
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Convexity.StdSimplex.weights_single`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x : M
),   (Convexity.StdSimple…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Convexity.StdSimplex.total`：∀ {R : Type u} [inst : LE R] [inst_1 : AddCo
mmMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   (
self.weights.sum…
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma support_weights_eq_singleton : w.weights.support = {x} ↔ w = single x where
  mp := by
    rw [support_eq_singleton']
    rintro ⟨a, ha, hwa⟩
    ext : 1
    simp only [hwa, weights_single]
    congr
    simpa [hwa] using w.total
  mpr := by rintro rfl; simp

/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
@[simps weights]
/-
**Convexity.StdSimplex.duple** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：duple (x y : M) {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) : St
dSimplex R M where weights
参数：x y : M；hs : 0 <= s；ht : 0 <= t；h : s + t = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A probability distribution with weight `s` on `x` and weight `t` on `y`.
-/
def duple (x y : M) {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) : StdSimplex R M where
  weights := .single x s + .single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by classical simpa [sum_add_index]

/--
Map a function over the support of a standard simplex.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
@[simps weights]
/-
**Convexity.StdSimplex.map** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：map {M : Type v} {N : Type w} (g : M -> N) (f : StdSimplex R M) : StdSimpl
ex R N where weights
参数：g : M -> N；f : StdSimplex R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function over the support of a standard simplex.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
def map {M : Type v} {N : Type w} (g : M → N) (f : StdSimplex R M) : StdSimplex R N where
  weights := f.weights.mapDomain g
  nonneg := f.weights.mapDomain_nonneg f.nonneg
  total := by simp [sum_mapDomain_index]

@[simp]
/-
**Convexity.StdSimplex.map_const** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex
`。
形式化陈述：map_const (f : StdSimplex R M) (x : N) : f.map (fun _ => x) = .single x
参数：f : StdSimplex R M；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.map.congr_simp`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Typ
e w}   (g g_1 : M → N),  …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Convexity.StdSimplex.total`：∀ {R : Type u} [inst : LE R] [inst_1 : AddCo
mmMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   (
self.weights.sum…
· 使用定理 `Convexity.StdSimplex.single.congr_simp`：∀ {R : Type u} [inst : PartialOr
der R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R]   (
x x_1 : M), x = x_1 → Convex…
· 使用定理 `Convexity.StdSimplex.weights_single`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x : M
),   (Convexity.StdSimple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
-/
lemma map_const (f : StdSimplex R M) (x : N) : f.map (fun _ ↦ x) = .single x := by
  ext a; by_cases x = a <;> simp [*, mapDomain]

@[simp]
/-
**Convexity.StdSimplex.map_single** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimple
x`。
形式化陈述：map_single (x : M) (f : M -> N) : (single (R
参数：x : M；f : M -> N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Convexity.StdSimplex.weights_single`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x : M
),   (Convexity.StdSimple…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_single (x : M) (f : M → N) : (single (R := R) x).map f = .single (f x) := by
  ext; simp

@[simp]
/-
**Convexity.StdSimplex.map_duple** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex
`。
形式化陈述：map_duple {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : M) 
(f : M -> N) : (duple x y hs ht h).map f = duple (f x) (f y) hs ht h
参数：hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y : M；f : M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Convexity.StdSimplex.weights_duple`：∀ {R : Type u} [inst : PartialOrder 
R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x y : 
M)   {s t : R} (hs : 0 ≤…
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_duple {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) (f : M → N) :
    (duple x y hs ht h).map f = duple (f x) (f y) hs ht h := by
  ext; simp [mapDomain_add]

@[simp]
/-
**Convexity.StdSimplex.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：map_id (f : StdSimplex R M) : f.map id = f
参数：f : StdSimplex R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (f : StdSimplex R M) : f.map id = f := by
  ext; simp
/-
**Convexity.StdSimplex.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex`
。
形式化陈述：map_comp (f : StdSimplex R M) (g₁ : M -> N) (g₂ : N -> P) : f.map (g₂ ∘ g₁
) = (f.map g₁).map g₂
参数：f : StdSimplex R M；g₁ : M -> N；g₂ : N -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    f.map (g₂ ∘ g₁) = (f.map g₁).map g₂ := by
  ext; simp [mapDomain_comp]
/-
**Convexity.StdSimplex.map_map** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：map_map (f : StdSimplex R M) (g₁ : M -> N) (g₂ : N -> P) : (f.map g₁).map 
g₂ = f.map (fun x => g₂ (g₁ x))
参数：f : StdSimplex R M；g₁ : M -> N；g₂ : N -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.StdSimplex.map_comp`：map_comp (f : StdSimplex R M) (g₁ : M -> 
N) (g₂ : N -> P) : f.map (g₂ ∘ g₁) = (f.map g₁).map g₂
-/
lemma map_map (f : StdSimplex R M) (g₁ : M → N) (g₂ : N → P) :
    (f.map g₁).map g₂ = f.map (fun x ↦ g₂ (g₁ x)) :=
  (map_comp ..).symm

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.

Use `ConvexSpace.sConvexComb` instead.
-/
@[simps weights]
/-
**Convexity.StdSimplex.join** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：join (f : StdSimplex R (StdSimplex R M)) : StdSimplex R M where weights
参数：f : StdSimplex R (StdSimplex R M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.

Use `ConvexSpace.sConvexComb` instead.
-/
def join (f : StdSimplex R (StdSimplex R M)) : StdSimplex R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  nonneg := f.weights.sum_nonneg fun d _ ↦ smul_nonneg (f.nonneg d) d.nonneg
  total := by simp [sum_sum_index, sum_smul_index, ← mul_sum]
/-
**Convexity.StdSimplex.join_join** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma join_join (f : StdSimplex R (StdSimplex R (StdSimplex R M))) :
    f.join.join = (f.map (·.join)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum, mul_smul]
/-
**Convexity.StdSimplex.map_join** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimplex`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma map_join (f : StdSimplex R (StdSimplex R M)) (g : M → N) :
    f.join.map g = (f.map (·.map g)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]
/-
**Convexity.StdSimplex.join_single** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdSimpl
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma join_single (x : StdSimplex R M) : join (.single x) = x := by
  ext; simp [join, ← mk_single]

end Semiring

section Semifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

/-
**Convexity.StdSimplex.restrict_nonneg_aux** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.
StdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma restrict_nonneg_aux {w : StdSimplex K X} {p : X → Prop} [DecidablePred p] :
    0 ≤ (filter p w.weights).sum fun _x k ↦ k :=
  sum_nonneg <| by simp [filter_apply, apply_ite]
/-
**Convexity.StdSimplex.restrict_ne_zero_aux** 是 Mathlib 中的一个引理，位于命名空间 `Convexity
.StdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma restrict_ne_zero_aux {w : StdSimplex K X} {p : X → Prop} [DecidablePred p]
    (hp : ∃ a, p a ∧ w.weights a ≠ 0) :
    (filter p w.weights).sum (fun _x k ↦ k) ≠ 0 :=
  (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by simpa [ne_iff, filter_apply]).ne'

/-- Project an element of the standard simplex to a lower-dimensional standard simplex,
assuming at least one non-zero weight subsists. -/
/-
**Convexity.StdSimplex.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.StdSimplex`
。
形式化陈述：restrict (w : StdSimplex K X) (s : Set X) (hs : exists x in s, w.weights x
 != 0) : StdSimplex K X where weights
参数：w : StdSimplex K X；s : Set X；hs : exists x in s, w.weights x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Project an element of the standard simplex to a lower-dimensional standard simpl
ex,
assuming at least one non-zero weight subsists.
-/
def restrict (w : StdSimplex K X) (s : Set X) (hs : ∃ x ∈ s, w.weights x ≠ 0) : StdSimplex K X where
  weights := open scoped Classical in
    ((w.weights.filter (· ∈ s)).sum fun x k ↦ k)⁻¹ • w.weights.filter (· ∈ s)
  nonneg := by
    classical
    exact smul_nonneg (inv_nonneg.2 restrict_nonneg_aux) fun _ ↦ by simp [filter_apply, apply_ite]
  total := by classical simp [sum_smul_index, ← mul_sum, restrict_ne_zero_aux hs]
/-
**Convexity.StdSimplex.weights_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.Std
Simplex`。
形式化陈述：weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· i
n s)] : (w.restrict s hs).weights = ((w.weights.filter (· in s)).sum fun _x k =>
 k)⁻¹ • w.weights.filter (· in s)
参数：w : StdSimplex K X；s : Set X；hs；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
lemma weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· ∈ s)] :
    (w.restrict s hs).weights =
      ((w.weights.filter (· ∈ s)).sum fun _x k ↦ k)⁻¹ • w.weights.filter (· ∈ s) := by
  simp [restrict]; congr

variable [IsDomain K]

@[simp]
/-
**Convexity.StdSimplex.support_weights_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Conve
xity.StdSimplex`。
形式化陈述：support_weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidableP
red (· in s)] : (w.restrict s hs).weights.support = w.weights.support.filter (· 
in s)
参数：w : StdSimplex K X；s : Set X；hs；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finsupp.sum_pos`：sum_pos (h : forall i in f.support, 0 < g i (f i)) (hf 
: f != 0) : 0 < f.sum g
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter_apply_pos`：filter_apply_pos {a : α} (h : p a) : f.filter 
p a = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Convexity.StdSimplex.weights_restrict`：weights_restrict (w : StdSimplex 
K X) (s : Set X) (hs) [DecidablePred (· in s)] : (w.restrict s hs).weights = ((w
.weights.filter (· in s)).s…
· 使用定理 `Finsupp.support_smul_eq`：support_smul_eq [Semiring R] [IsDomain R] [AddC
ommMonoid M] [Module R M] [Module.IsTorsionFree R M] {b : R} (hb : b != 0) {g : 
α ->₀ M} : (b…
· 使用定理 `instIsTorsionFree`：∀ {R : Type u_1} [inst : Semiring R], Module.IsTorsio
nFree R R
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· ∈ s)] :
    (w.restrict s hs).weights.support = w.weights.support.filter (· ∈ s) := by
  have : (w.weights.filter (· ∈ s)).sum (fun x k ↦ k) ≠ 0 :=
    (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by
      simpa [ne_iff, filter_apply]).ne'
  rw [weights_restrict, support_smul_eq (by convert inv_ne_zero this)]
  simp
/-
**Convexity.StdSimplex.restrict_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.S
tdSimplex`。
形式化陈述：∀ {X : Type u_2} {K : Type u_8} [inst : Semifield K] [inst_1 : LinearOrder
 K] [inst_2 : IsStrictOrderedRing K]   [IsDomain K] (w : Convexity.StdSimplex K 
X) (x : X) (hx : ∃ x_1 ∈ {x}, w.weights x_1 ≠ 0),   w.restrict {x} hx = Convexit
y.StdSimplex.single x
参数：w : Convexity.StdSimplex K X；x : X；hx : ∃ x_1 ∈ {x}, w.weights x_1 ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.support_weights_restrict`：support_weights_restrict 
(w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· in s)] : (w.restrict s h
s).weights.support = w.weights.supp…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma restrict_singleton (w : StdSimplex K X) (x : X) (hx) :
    w.restrict {x} hx = single x := by
  classical
  simp only [← support_weights_eq_singleton, support_weights_restrict, Set.mem_singleton_iff]
  ext
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
  rintro rfl
  simpa using hx

end Semifield
end StdSimplex

/--
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
/-
**Convexity.ConvexSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Convexity`。
形式化陈述：(R : Type u) →   Type v → [inst₁ : PartialOrder R] → [inst₂ : Semiring R] 
→ [inst₃ : IsStrictOrderedRing R] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set equipped with an operation of finite convex combinations,
where the coefficients must be non-negative and sum to 1.
-/
class ConvexSpace (R : Type u) (M : Type v)
    [inst₁ : PartialOrder R] [inst₂ : Semiring R] [inst₃ : IsStrictOrderedRing R] where
  /-- Use `mk` instead. -/
  mk' ::
  /-- Take a convex combination with the given probability distribution over points. -/
  /- FIXME: Lean makes `inst₁`, `inst₂`, `inst₃` implicit by default, which renders `sConvexComb`
  unusable without these manual `[inst]` binders. Why is this so? Shouldn't typeclass arguments to
  a `structure` also be typeclass arguments to its fields? -/
  sConvexComb [inst₁] [inst₂] [inst₃] (f : StdSimplex R M) : M
  /-- A convex combination of a single point is that point. -/
  sConvexComb_single (x : M) : sConvexComb (.single x) = x
  /-- Associativity of convex combination (monadic join law).

  Use `sConvexComb_sConvexComb` instead. -/
  assoc (f : StdSimplex R (StdSimplex R M)) :
    sConvexComb (f.map sConvexComb) = sConvexComb f.join

open ConvexSpace StdSimplex

variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N] [ConvexSpace R P]

export ConvexSpace (sConvexComb sConvexComb_single)

attribute [simp] sConvexComb_single

@[deprecated (since := "2026-05-04")] alias ConvexSpace.convexCombination := sConvexComb

@[deprecated (since := "2026-05-04")]
alias ConvexSpace.convexCombination_single := sConvexComb_single

/-- Take a convex combination with the given weight distribution of an indexed family of points. -/
/-
**Convexity.iConvexComb** 是 Mathlib 中的一个定义，位于命名空间 `Convexity`。
形式化陈述：iConvexComb (s : StdSimplex R I) (f : I -> M) : M
参数：s : StdSimplex R I；f : I -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take a convex combination with the given weight distribution of an indexed famil
y of points.
-/
def iConvexComb (s : StdSimplex R I) (f : I → M) : M := sConvexComb (s.map f)

/-- Take a convex combination of two points. -/
/-
**Convexity.convexCombPair** 是 Mathlib 中的一个定义，位于命名空间 `Convexity`。
形式化陈述：convexCombPair (s t : R) (hs : 0 <= s) (ht : 0 <= t) (hst : s + t = 1) (x 
y : M) : M
参数：s t : R；hs : 0 <= s；ht : 0 <= t；hst : s + t = 1；x y : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take a convex combination of two points.
-/
def convexCombPair (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (x y : M) : M :=
  sConvexComb (.duple x y hs ht hst)

@[deprecated (since := "2026-05-15")] alias convexComboPair := convexCombPair

namespace StdSimplex

-- We export `sConvexComb` and `iConvexComb` to allow dot notation on the `StdSimplex` argument.
export ConvexSpace (sConvexComb)
export Convexity (iConvexComb)

/-
**Convexity.StdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `Convexity.StdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConvexSpace R (StdSimplex R I) where
  sConvexComb σ := σ.join
  assoc f := by exact (join_join f).symm
  sConvexComb_single := by exact join_single
/-
**Convexity.StdSimplex.weights_sConvexComb** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.
StdSimplex`。
形式化陈述：∀ {R : Type u_1} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring
 R] [inst_2 : IsStrictOrderedRing R]   (f : Convexity.StdSimplex R (Convexity.St
dSimplex R I)),   (Convexity.sConvexComb f).weights = f.weights.sum fun d r => r
 • d.weights
参数：f : Convexity.StdSimplex R (Convexity.StdSimplex R I)；Convexity.sConvexComb f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.weights_join`：∀ {R : Type u} [inst : PartialOrder R
] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R]   (f : C
onvexity.StdSimplex R (…
-/
@[simp] lemma weights_sConvexComb (f : StdSimplex R (StdSimplex R I)) :
    f.sConvexComb.weights = f.weights.sum (fun d r => r • d.weights) :=
  StdSimplex.weights_join _
/-
**Convexity.StdSimplex.weights_iConvexComb** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.
StdSimplex`。
形式化陈述：∀ {R : Type u_1} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring
 R] [inst_2 : IsStrictOrderedRing R]   (w : Convexity.StdSimplex R I) (f : I → C
onvexity.StdSimplex R I),   (Convexity.iConvexComb w f).weights = w.weights.sum 
fun i r => r • (f i).weights
参数：w : Convexity.StdSimplex R I；f : I → Convexity.StdSimplex R I；Convexity.iConv
exComb w f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_sConvexComb`：∀ {R : Type u_1} {I : Type u_6
} [inst : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]
   (f : Convexity.StdSimplex R…
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
@[simp] lemma weights_iConvexComb (w : StdSimplex R I) (f : I → StdSimplex R I) :
    (iConvexComb w f).weights = w.weights.sum (fun i r => r • (f i).weights) := by
  simp [iConvexComb, sum_mapDomain_index, add_smul]
/-
**Convexity.StdSimplex.weights_convexCombPair** 是 Mathlib 中的一个定理，位于命名空间 `Convexi
ty.StdSimplex`。
形式化陈述：∀ {R : Type u_1} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring
 R] [inst_2 : IsStrictOrderedRing R]   (w w' : Convexity.StdSimplex R I) (s t : 
R) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1),   (Convexity.convexCombPair s t 
hs ht hst w w').weights = s • w.weights + t • w'.weights
参数：w w' : Convexity.StdSimplex R I；s t : R；hs : 0 ≤ s；ht : 0 ≤ t；hst : s + t = 1
；Convexity.convexCombPair s t hs ht hst w w'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_sConvexComb`：∀ {R : Type u_1} {I : Type u_6
} [inst : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]
   (f : Convexity.StdSimplex R…
· 使用定理 `Convexity.StdSimplex.weights_duple`：∀ {R : Type u} [inst : PartialOrder 
R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x y : 
M)   {s t : R} (hs : 0 ≤…
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
@[simp] lemma weights_convexCombPair (w w' : StdSimplex R I) (s t : R) (hs ht hst) :
    (convexCombPair s t hs ht hst w w').weights = s • w.weights + t • w'.weights := by
  classical simp [convexCombPair, sum_add_index, add_smul]
/-
**Convexity.StdSimplex.map_sConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexity.StdS
implex`。
形式化陈述：map_sConvexComb (s : StdSimplex R (StdSimplex R I)) (f : I -> J) : s.sConv
exComb.map f = (s.map (map f)).sConvexComb
参数：s : StdSimplex R (StdSimplex R I)；f : I -> J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Geometry.Convex.ConvexSpace.Defs.0.Convexity.StdSimplex
.map_join`：∀ {R : Type u} [inst : PartialOrder R] [inst_1 : Semiring R] {M : Typ
e u_9} {N : Type u_10}   [inst_2 : IsStrictOrderedRing R] (f : Convexit…
-/
lemma map_sConvexComb (s : StdSimplex R (StdSimplex R I)) (f : I → J) :
    s.sConvexComb.map f = (s.map (map f)).sConvexComb :=
  StdSimplex.map_join s f

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
/-
**Convexity.StdSimplex.convexCombPair_restrict_restrict_compl** 是 Mathlib 中的一个引理
，位于命名空间 `Convexity.StdSimplex`。
形式化陈述：convexCombPair_restrict_restrict_compl (w : StdSimplex K I) (s : Set I) (h
s hs') [DecidablePred (· in s)] : convexCombPair ((w.weights.filter (· in s)).su
m fun _x k => k) ((w.weights.filter (· ∉ s)).sum fun _x k => k) (by exact restri
ct_nonneg_aux) (by exact restrict_nonneg_aux) (by simp) (w.restrict s hs) (w.res
trict sᶜ hs') = w
参数：w : StdSimplex K I；s : Set I；hs hs'；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_convexCombPair`：∀ {R : Type u_1} {I : Type 
u_6} [inst : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing
 R]   (w w' : Convexity.StdSimple…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Convexity.StdSimplex.weights_restrict`：weights_restrict (w : StdSimplex 
K X) (s : Set X) (hs) [DecidablePred (· in s)] : (w.restrict s hs).weights = ((w
.weights.filter (· in s)).s…
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.filter.congr_simp`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (p p_1 : α → Prop),   p = p_1 →     ∀ {inst_1 : DecidablePred p} [inst_2 : De
cidablePred p_1…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finsupp.filter_add_filter_not`：filter_add_filter_not (f : α ->₀ M) (p : 
α -> Prop) [DecidablePred p] : f.filter p + f.filter (¬ p ·) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convexCombPair_restrict_restrict_compl (w : StdSimplex K I) (s : Set I) (hs hs')
    [DecidablePred (· ∈ s)] :
    convexCombPair
      ((w.weights.filter (· ∈ s)).sum fun _x k ↦ k)
      ((w.weights.filter (· ∉ s)).sum fun _x k ↦ k)
      (by exact restrict_nonneg_aux) (by exact restrict_nonneg_aux) (by simp)
      (w.restrict s hs) (w.restrict sᶜ hs') = w := by
  ext : 1
  simp only [Set.mem_compl_iff] at hs'
  simp [weights_restrict, smul_inv_smul₀, restrict_ne_zero_aux, hs, hs']

end StdSimplex

/-
**Convexity.sConvexComb_sConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：sConvexComb_sConvexComb (f : StdSimplex R (StdSimplex R M)) : f.sConvexCom
b.sConvexComb = (f.map sConvexComb).sConvexComb
参数：f : StdSimplex R (StdSimplex R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convexity.ConvexSpace.assoc`：∀ {R : Type u} {M : Type v} {inst₁ : Partia
lOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [self : Convexi
ty.ConvexSpace R …
-/
lemma sConvexComb_sConvexComb (f : StdSimplex R (StdSimplex R M)) :
    f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvexComb :=
  (ConvexSpace.assoc f).symm
/-
**Convexity.sConvexComb_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：sConvexComb_convexCombPair (s t : R) (hs ht hst) (w w' : StdSimplex R M) :
 (convexCombPair s t hs ht hst w w').sConvexComb = convexCombPair s t hs ht hst 
w.sConvexComb w'.sConvexComb
参数：s t : R；hs ht hst；w w' : StdSimplex R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.sConvexComb_sConvexComb`：sConvexComb_sConvexComb (f : StdSimpl
ex R (StdSimplex R M)) : f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvex
Comb
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sConvexComb_convexCombPair (s t : R) (hs ht hst) (w w' : StdSimplex R M) :
    (convexCombPair s t hs ht hst w w').sConvexComb =
      convexCombPair s t hs ht hst w.sConvexComb w'.sConvexComb := by
  simp [convexCombPair, sConvexComb_sConvexComb]

/-- The public constructor for `ConvexSpace`. -/
/-
**Convexity.ConvexSpace.mk** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.ConvexSpace`。
形式化陈述：{R : Type u_1} →   [inst : PartialOrder R] →     [inst_1 : Semiring R] →  
     [inst_2 : IsStrictOrderedRing R] →         {M : Type u_9} →           (sCon
vexComb : Convexity.StdSimplex R M → M) →             (∀ (x : M), sConvexComb (C
onvexity.StdSimplex.single x) = x) →               (∀ (f : Convexity.StdSimplex 
R (Convexity.StdSimplex R M)),                   sConvexComb (Convexity.StdSimpl
ex.map sConvexComb f) = sConvexComb (Convexity.sConvexComb f)) →                
 Convexity.ConvexSpace R M
参数：sConvexComb : Convexity.StdSimplex R M → M；∀ (x : M), sConvexComb (Convexity.
StdSimplex.single x) = x；∀ (f : Convexity.StdSimplex R (Convexity.StdSimplex R M
)),                   sConvexComb (Convexity.StdSimplex.map sConvexComb f) = sCo
nvexComb (Convexity.sConvexComb f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The public constructor for `ConvexSpace`.
-/
abbrev ConvexSpace.mk {M : Type*} (sConvexComb : StdSimplex R M → M)
    (single : ∀ x : M, sConvexComb (.single x) = x)
    (assoc : ∀ f : StdSimplex R (StdSimplex R M),
      sConvexComb (f.map sConvexComb) = sConvexComb f.sConvexComb) : ConvexSpace R M :=
  ⟨sConvexComb, single, assoc⟩

variable (R) in
/-- A map between convex spaces is affine if it preserves convex combinations.

TODO: Show that this generalises affine maps between affine spaces, see `AffineMap`. -/
@[fun_prop]
/-
**Convexity.IsAffineMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Convexity`。
形式化陈述：(R : Type u_1) →   {M : Type u_3} →     {N : Type u_4} →       [inst : Par
tialOrder R] →         [inst_1 : Semiring R] →           [inst_2 : IsStrictOrder
edRing R] → [Convexity.ConvexSpace R M] → [Convexity.ConvexSpace R N] → (M → N) 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map between convex spaces is affine if it preserves convex combinations.

TODO: Show that this generalises affine maps between affine spaces, see `AffineM
ap`.
-/
structure IsAffineMap (f : M → N) : Prop where
  map_sConvexComb (s : StdSimplex R M) : f s.sConvexComb = (s.map f).sConvexComb

@[fun_prop]
/-
**Convexity.IsAffineMap.id** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsAffineMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : PartialOrder R] [inst_1 : Semiring
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R M], Con
vexity.IsAffineMap R id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_id`：map_id (f : StdSimplex R M) : f.map id = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma IsAffineMap.id : IsAffineMap R (id : M → M) where
  map_sConvexComb s := by simp

@[fun_prop]
/-
**Convexity.IsAffineMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsAffineMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_4} {P : Type u_5} [inst : Part
ialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : C
onvexity.ConvexSpace R M] [inst_4 : Convexity.ConvexSpace R N]   [inst_5 : Conve
xity.ConvexSpace R P] {g : N → P},   Convexity.IsAffineMap R g → ∀ {f : M → N}, 
Convexity.IsAffineMap R f → Convexity.IsAffineMap R (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsAffineMap.map_sConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Co…
· 使用引理 `Convexity.StdSimplex.map_comp`：map_comp (f : StdSimplex R M) (g₁ : M -> 
N) (g₂ : N -> P) : f.map (g₂ ∘ g₁) = (f.map g₁).map g₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsAffineMap.comp {g : N → P} (hg : IsAffineMap R g) {f : M → N} (hf : IsAffineMap R f) :
    IsAffineMap R (g ∘ f) where
  map_sConvexComb s := by
    simp [StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb]

@[fun_prop]
/-
**Convexity.IsAffineMap.const** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsAffineMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_4} [inst : PartialOrder R] [in
st_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R M] [inst_4 : Convexity.ConvexSpace R N] (x : N),   Convexity.IsAffineMap
 R fun x_1 => x
参数：x : N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_const`：map_const (f : StdSimplex R M) (x : N) :
 f.map (fun _ => x) = .single x
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsAffineMap.const (x : N) :
    IsAffineMap R (fun (_ : M) ↦ x) where
  map_sConvexComb _ := by simp

variable (R) in
@[fun_prop]
/-
**Convexity.StdSimplex.isAffineMap_map** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.StdS
implex`。
形式化陈述：∀ (R : Type u_1) {I : Type u_6} {J : Type u_7} [inst : PartialOrder R] [in
st_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] (f : I → J), Convexity.IsA
ffineMap R (Convexity.StdSimplex.map f)
参数：R : Type u_1；f : I → J；Convexity.StdSimplex.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
-/
lemma StdSimplex.isAffineMap_map (f : I → J) : IsAffineMap R (StdSimplex.map (R := R) f) :=
  ⟨(map_sConvexComb · f)⟩

section iConvexComb

/-
**Convexity.sConvexComb_map** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：sConvexComb_map (w : StdSimplex R I) (f : I -> M) : sConvexComb (w.map f) 
= iConvexComb w f
参数：w : StdSimplex R I；f : I -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sConvexComb_map (w : StdSimplex R I) (f : I → M) :
    sConvexComb (w.map f) = iConvexComb w f := rfl
/-
**Convexity.iConvexComb_const** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6} [inst : PartialOrder R] [in
st_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R M] (s : Convexity.StdSimplex R I) (m : M),   (Convexity.iConvexComb s fu
n x => m) = m
参数：s : Convexity.StdSimplex R I；m : M；Convexity.iConvexComb s fun x => m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_const`：map_const (f : StdSimplex R M) (x : N) :
 f.map (fun _ => x) = .single x
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma iConvexComb_const (s : StdSimplex R I) (m : M) :
    s.iConvexComb (fun _ ↦ m) = m := by simp [iConvexComb]
/-
**Convexity.iConvexComb_single** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6} [inst : PartialOrder R] [in
st_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R M] (i : I) (f : I → M),   Convexity.iConvexComb (Convexity.StdSimplex.si
ngle i) f = f i
参数：i : I；f : I → M；Convexity.StdSimplex.single i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_single`：map_single (x : M) (f : M -> N) : (sing
le (R
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma iConvexComb_single (i : I) (f : I → M) :
    (single (R := R) i).iConvexComb f = f i := by simp [iConvexComb]
/-
**Convexity.iConvexComb_id** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_id (w : StdSimplex R M) : w.iConvexComb id = w.sConvexComb
参数：w : StdSimplex R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_id`：map_id (f : StdSimplex R M) : f.map id = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iConvexComb_id (w : StdSimplex R M) : w.iConvexComb id = w.sConvexComb := by
  simp [iConvexComb]
/-
**Convexity.iConvexComb_id'** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : PartialOrder R] [inst_1 : Semiring
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R M] (w :
 Convexity.StdSimplex R M),   (Convexity.iConvexComb w fun x => x) = Convexity.s
ConvexComb w
参数：w : Convexity.StdSimplex R M；Convexity.iConvexComb w fun x => x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Convexity.iConvexComb_id`：iConvexComb_id (w : StdSimplex R M) : w.iConve
xComb id = w.sConvexComb
-/
@[simp] lemma iConvexComb_id' (w : StdSimplex R M) :
    w.iConvexComb (fun x ↦ x) = w.sConvexComb := iConvexComb_id _
/-
**Convexity.iConvexComb_map** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6} {J : Type u_7} [inst : Part
ialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : C
onvexity.ConvexSpace R M] (s : Convexity.StdSimplex R I) (f : I → J)   (g : J → 
M), Convexity.iConvexComb (Convexity.StdSimplex.map f s) g = Convexity.iConvexCo
mb s fun i => g (f i)
参数：s : Convexity.StdSimplex R I；f : I → J；g : J → M；Convexity.StdSimplex.map f s
；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma iConvexComb_map (s : StdSimplex R I) (f : I → J) (g : J → M) :
    (s.map f).iConvexComb g = s.iConvexComb (fun i ↦ g (f i)) := by
  simp only [iConvexComb, map_map]
/-
**Convexity.iConvexComb_congr** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6} [inst : PartialOrder R] [in
st_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R M] {w : Convexity.StdSimplex R I} {f g : I → M},   (∀ (i : I), w.weights
 i ≠ 0 → f i = g i) → Convexity.iConvexComb w f = Convexity.iConvexComb w g
参数：∀ (i : I), w.weights i ≠ 0 → f i = g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.mapDomain_congr`：mapDomain_congr {f g : α -> β} (h : forall x in
 v.support, f x = g x) : v.mapDomain f = v.mapDomain g
-/
@[congr] lemma iConvexComb_congr {w : StdSimplex R I} {f g : I → M}
    (hfg : ∀ i, w.weights i ≠ 0 → f i = g i) :
    w.iConvexComb f = w.iConvexComb g := by
  refine congr(sConvexComb $(?_))
  ext i
  simp only [weights_map]
  -- TODO: This should just be `congr! 2 with i hi`.
  congr 1
  refine Finsupp.mapDomain_congr fun i hi ↦ ?_
  exact hfg i (by simpa using hi)
/-
**Convexity.iConvexComb_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_reindex (s : StdSimplex R I) (f : I ≃ J) (g : I -> M) : s.iCon
vexComb g = (s.map f).iConvexComb (g ∘ f.symm)
参数：s : StdSimplex R I；f : I ≃ J；g : I -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.iConvexComb_map`：∀ {R : Type u_1} {M : Type u_3} {I : Type u_6
} {J : Type u_7} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing …
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iConvexComb_reindex (s : StdSimplex R I) (f : I ≃ J) (g : I → M) :
    s.iConvexComb g = (s.map f).iConvexComb (g ∘ f.symm) := by
  simp [iConvexComb_map]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'` and `iConvexComb_assoc` for non-dependent versions. -/
/-
**Convexity.iConvexComb_assoc''** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_assoc'' {J : I -> Type*} (s : StdSimplex R I) (f : Π i, StdSim
plex R (J i)) (g : Π i, J i -> M) : s.iConvexComb (fun i => (f i).iConvexComb (g
 i)) = (s.iConvexComb fun i => (f i).map (⟨i, ·⟩)).iConvexComb (Sigma.uncurry g)
参数：s : StdSimplex R I；f : Π i, StdSimplex R (J i)；g : Π i, J i -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))
· 使用引理 `Convexity.sConvexComb_sConvexComb`：sConvexComb_sConvexComb (f : StdSimpl
ex R (StdSimplex R M)) : f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvex
Comb
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
· 使用定理 `Convexity.StdSimplex.map.congr_simp`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Typ
e w}   (g g_1 : M → N),  …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'` and `iConvexComb_assoc` for non-dependent versions.
-/
lemma iConvexComb_assoc''
    {J : I → Type*} (s : StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i → M) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i ↦ (f i).map (⟨i, ·⟩)).iConvexComb (Sigma.uncurry g) := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Sigma.uncurry]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc''` for a more dependent version, and `iConvexComb_assoc`
for a less dependent one. -/
/-
**Convexity.iConvexComb_assoc'** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_assoc' {J : Type*} (s : StdSimplex R I) (f : I -> StdSimplex R
 J) (g : I -> J -> M) : s.iConvexComb (fun i => (f i).iConvexComb (g i)) = (s.iC
onvexComb fun i => (f i).map (⟨i, ·⟩)).iConvexComb g.uncurry
参数：s : StdSimplex R I；f : I -> StdSimplex R J；g : I -> J -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))
· 使用引理 `Convexity.sConvexComb_sConvexComb`：sConvexComb_sConvexComb (f : StdSimpl
ex R (StdSimplex R M)) : f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvex
Comb
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
· 使用定理 `Convexity.StdSimplex.map.congr_simp`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Typ
e w}   (g g_1 : M → N),  …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Flattening nested `iConvexComb`s.

See `iConvexComb_assoc''` for a more dependent version, and `iConvexComb_assoc`
for a less dependent one.
-/
lemma iConvexComb_assoc' {J : Type*} (s : StdSimplex R I) (f : I → StdSimplex R J)
    (g : I → J → M) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i ↦ (f i).map (⟨i, ·⟩)).iConvexComb g.uncurry := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Function.uncurry]

/-- Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'`, `iConvexComb_assoc''` for more dependent versions. -/
/-
**Convexity.iConvexComb_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_assoc {J : Type*} (s : StdSimplex R I) (f : I -> StdSimplex R 
J) (g : J -> M) : s.iConvexComb (fun i => (f i).iConvexComb g) = (s.iConvexComb 
f).iConvexComb g
参数：s : StdSimplex R I；f : I -> StdSimplex R J；g : J -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))
· 使用引理 `Convexity.sConvexComb_sConvexComb`：sConvexComb_sConvexComb (f : StdSimpl
ex R (StdSimplex R M)) : f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvex
Comb
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Flattening nested `iConvexComb`s.

See `iConvexComb_assoc'`, `iConvexComb_assoc''` for more dependent versions.
-/
lemma iConvexComb_assoc {J : Type*} (s : StdSimplex R I) (f : I → StdSimplex R J)
    (g : J → M) :
    s.iConvexComb (fun i ↦ (f i).iConvexComb g) = (s.iConvexComb f).iConvexComb g := by
  simp only [iConvexComb]
  rw [← map_map, ← sConvexComb_sConvexComb]
  simp [map_sConvexComb, map_map]

variable {R M I J : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] in
/-
**Convexity.iConvexComb_comm** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_comm (f : StdSimplex R I) (g : StdSimplex R J) (e : I -> J -> 
M) : f.iConvexComb (fun i => g.iConvexComb (e i)) = g.iConvexComb fun j => f.iCo
nvexComb fun i => e i j
参数：f : StdSimplex R I；g : StdSimplex R J；e : I -> J -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.iConvexComb_assoc'`：iConvexComb_assoc' {J : Type*} (s : StdSim
plex R I) (f : I -> StdSimplex R J) (g : I -> J -> M) : s.iConvexComb (fun i => 
(f i).iConvexComb …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Convexity.iConvexComb_reindex`：iConvexComb_reindex (s : StdSimplex R I) 
(f : I ≃ J) (g : I -> M) : s.iConvexComb g = (s.map f).iConvexComb (g ∘ f.symm)
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Convexity.StdSimplex.weights_sConvexComb`：∀ {R : Type u_1} {I : Type u_6
} [inst : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]
   (f : Convexity.StdSimplex R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finsupp.sum_sum_index`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} {P : Type u_11} [inst : Zero M]   [inst_1 : AddCommMonoid N] [inst
_2 : AddCom…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Finsupp.sum_comm`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {M' : T
ype u_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommM
onoid …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))
· 使用定理 `Convexity.StdSimplex.map.congr_simp`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Typ
e w}   (g g_1 : M → N),  …
-/
lemma iConvexComb_comm (f : StdSimplex R I) (g : StdSimplex R J)
    (e : I → J → M) :
    f.iConvexComb (fun i ↦ g.iConvexComb (e i)) =
      g.iConvexComb fun j ↦ f.iConvexComb fun i ↦ e i j := by
  rw [iConvexComb_assoc', iConvexComb_assoc', iConvexComb_reindex _ (.prodComm ..)]
  congr
  suffices (f.map fun x ↦ g.map (Prod.mk · x)).sConvexComb =
      (g.map (f.map ∘ Prod.mk)).sConvexComb by
    simpa [iConvexComb, map_sConvexComb, map_map, Function.comp_def]
  ext1
  simp [mapDomain, sum_sum_index, add_smul, smul_sum, mul_comm, sum_comm f.weights g.weights]
/-
**Convexity.IsAffineMap.map_iConvexComb** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsA
ffineMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_4} {I : Type u_6} [inst : Part
ialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : C
onvexity.ConvexSpace R M] [inst_4 : Convexity.ConvexSpace R N]   {f : M → N},   
Convexity.IsAffineMap R f →     ∀ (s : Convexity.StdSimplex R I) (g : I → M), f 
(Convexity.iConvexComb s g) = Convexity.iConvexComb s (f ∘ g)
参数：s : Convexity.StdSimplex R I；g : I → M；Convexity.iConvexComb s g；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsAffineMap.map_sConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Co…
· 使用引理 `Convexity.StdSimplex.map_comp`：map_comp (f : StdSimplex R M) (g₁ : M -> 
N) (g₂ : N -> P) : f.map (g₂ ∘ g₁) = (f.map g₁).map g₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsAffineMap.map_iConvexComb {f : M → N} (hf : IsAffineMap R f)
    (s : StdSimplex R I) (g : I → M) : f (s.iConvexComb g) = s.iConvexComb (f ∘ g) := by
  simp [iConvexComb, hf.map_sConvexComb, map_comp]
/-
**Convexity.map_iConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：map_iConvexComb {f : J -> K} (s : StdSimplex R I) (g : I -> StdSimplex R J
) : (s.iConvexComb g).map f = s.iConvexComb (map f ∘ g)
参数：s : StdSimplex R I；g : I -> StdSimplex R J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
· 使用定理 `Convexity.StdSimplex.isAffineMap_map`：∀ (R : Type u_1) {I : Type u_6} {J
 : Type u_7} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictO
rderedRing R] (f : I → J),…
-/
lemma map_iConvexComb {f : J → K}
    (s : StdSimplex R I) (g : I → StdSimplex R J) :
    (s.iConvexComb g).map f = s.iConvexComb (map f ∘ g) :=
  (isAffineMap_map R f).map_iConvexComb s g

end iConvexComb

variable {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)
variable {s' t' : R} (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h' : s' + t' = 1)
variable {s'' t'' : R} (hs'' : 0 ≤ s'') (ht'' : 0 ≤ t'') (h'' : s'' + t'' = 1)

/-
**Convexity.convexCombPair_def** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_def (p q : M) : convexCombPair s t hs ht h p q = (StdSimple
x.duple 0 1 hs ht h).iConvexComb ![p, q]
参数：p q : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用定理 `Convexity.StdSimplex.duple.congr_simp`：∀ {R : Type u} [inst : PartialOrd
er R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R]   (x
 x_1 : M),   x = x_1 →     …
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convexCombPair_def (p q : M) :
    convexCombPair s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexComb ![p, q] := by
  simp [StdSimplex.iConvexComb, convexCombPair]

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
@[simp]
/-
**Convexity.convexCombPair_zero** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_zero {x y : M} : convexCombPair (0 : R) 1 (by simp) (by sim
p) (by simp) x y = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.mk.congr_simp`：∀ {R : Type u} [inst : LE R] [inst_1
 : AddCommMonoid R] [inst_2 : One R] {M : Type v} (weights weights_1 : M →₀ R)  
 (e_weights : weights = …
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A binary convex combination with weight 0 on the first point returns the second 
point.
-/
theorem convexCombPair_zero {x y : M} :
    convexCombPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_zero := convexCombPair_zero

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
@[simp]
/-
**Convexity.convexCombPair_one** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_one {x y : M} : convexCombPair (1 : R) 0 (by simp) (by simp
) (by simp) x y = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.mk.congr_simp`：∀ {R : Type u} [inst : LE R] [inst_1
 : AddCommMonoid R] [inst_2 : One R] {M : Type v} (weights weights_1 : M →₀ R)  
 (e_weights : weights = …
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A binary convex combination with weight 1 on the first point returns the first p
oint.
-/
theorem convexCombPair_one {x y : M} :
    convexCombPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_one := convexCombPair_one

/-- A convex combination of a point with itself is that point. -/
@[simp]
/-
**Convexity.convexCombPair_same** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_same {x : M} : convexCombPair s t hs ht h x x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.mk.congr_simp`：∀ {R : Type u} [inst : LE R] [inst_1
 : AddCommMonoid R] [inst_2 : One R] {M : Type v} (weights weights_1 : M →₀ R)  
 (e_weights : weights = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …

--- 原说明 ---
A convex combination of a point with itself is that point.
-/
theorem convexCombPair_same {x : M} :
    convexCombPair s t hs ht h x x = x := by
  unfold convexCombPair
  convert sConvexComb_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← single_add, h]

@[deprecated (since := "2026-05-15")] alias convexComboPair_symm := convexCombPair_same
/-
**Convexity.convexCombPair_symm** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_symm {x y : M} : convexCombPair s t hs ht h x y = convexCom
bPair t s ht hs ((add_comm _ _).trans h) y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.mk.congr_simp`：∀ {R : Type u} [inst : LE R] [inst_1
 : AddCommMonoid R] [inst_2 : One R] {M : Type v} (weights weights_1 : M →₀ R)  
 (e_weights : weights = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexCombPair_symm {x y : M} :
    convexCombPair s t hs ht h x y = convexCombPair t s ht hs ((add_comm _ _).trans h) y x := by
  unfold convexCombPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]
/-
**Convexity.IsAffineMap.map_convexCombPair** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.
IsAffineMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_4} [inst : PartialOrder R] [in
st_1 : Semiring R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R M] [inst_4 : Convexity.ConvexSpace R N]   {f : M → N},   Convexity.IsAff
ineMap R f →     ∀ {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M)
,       f (Convexity.convexCombPair s t hs ht h x y) = Convexity.convexCombPair 
s t hs ht h (f x) (f y)
参数：hs : 0 ≤ s；ht : 0 ≤ t；h : s + t = 1；x y : M；Convexity.convexCombPair s t hs h
t h x y；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsAffineMap.map_sConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Co…
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsAffineMap.map_convexCombPair {f : M → N} (hf : IsAffineMap R f)
    {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : M) :
    f (convexCombPair s t hs ht h x y) = convexCombPair s t hs ht h (f x) (f y) := by
  simp [hf.map_sConvexComb, convexCombPair]

set_option backward.isDefEq.respectTransparency.types false in
/-- Flattening with the outer combination specialized to `convexCombPair`. -/
/-
**Convexity.convexCombPair_iConvexComb_iConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Co
nvexity`。
形式化陈述：convexCombPair_iConvexComb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂} (g₁ :
 StdSimplex R J₁) (g₂ : StdSimplex R J₂) (m₁ : J₁ -> M) (m₂ : J₂ -> M) : convexC
ombPair s t hs ht h (g₁.iConvexComb m₁) (g₂.iConvexComb m₂) = (convexCombPair s 
t hs ht h (g₁.map m₁) (g₂.map m₂)).sConvexComb
参数：g₁ : StdSimplex R J₁；g₂ : StdSimplex R J₂；m₁ : J₁ -> M；m₂ : J₂ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Convexity.iConvexComb_assoc''`：iConvexComb_assoc'' {J : I -> Type*} (s :
 StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i -> M) : s.iConvexCo
mb (fun i => (f i).…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用定理 `Convexity.StdSimplex.duple.congr_simp`：∀ {R : Type u} [inst : PartialOrd
er R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R]   (x
 x_1 : M),   x = x_1 →     …
· 使用定理 `Convexity.StdSimplex.map.congr_simp`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Typ
e w}   (g g_1 : M → N),  …
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
Flattening with the outer combination specialized to `convexCombPair`.
-/
lemma convexCombPair_iConvexComb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂}
    (g₁ : StdSimplex R J₁) (g₂ : StdSimplex R J₂)
    (m₁ : J₁ → M) (m₂ : J₂ → M) :
    convexCombPair s t hs ht h (g₁.iConvexComb m₁) (g₂.iConvexComb m₂) =
      (convexCombPair s t hs ht h (g₁.map m₁) (g₂.map m₂)).sConvexComb := by
  have := iConvexComb_assoc'' (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexComb, map_sConvexComb, map_map, Sigma.uncurry] at this
  simpa [convexCombPair, ← convexCombPair_def]

/-- Flattening with the inner combination specialized to `convexCombPair`. -/
/-
**Convexity.iConvexComb_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：iConvexComb_convexCombPair (s t : I -> R) (hs : forall i, 0 <= s i) (ht : 
forall i, 0 <= t i) (h : forall i, s i + t i = 1) (f : StdSimplex R I) (m₁ m₂ : 
I -> M) : f.iConvexComb (fun i => convexCombPair (s i) (t i) (hs i) (ht i) (h i)
 (m₁ i) (m₂ i)) = (f.iConvexComb fun i => duple (m₁ i) (m₂ i) (hs i) (ht i) (h i
)).sConvexComb
参数：s t : I -> R；hs : forall i, 0 <= s i；ht : forall i, 0 <= t i；h : forall i, s 
i + t i = 1；f : StdSimplex R I；m₁ m₂ : I -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Convexity.iConvexComb_assoc'`：iConvexComb_assoc' {J : Type*} (s : StdSim
plex R I) (f : I -> StdSimplex R J) (g : I -> J -> M) : s.iConvexComb (fun i => 
(f i).iConvexComb …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.map.congr_simp`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Typ
e w}   (g g_1 : M → N),  …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用定理 `Convexity.StdSimplex.duple.congr_simp`：∀ {R : Type u} [inst : PartialOrd
er R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R]   (x
 x_1 : M),   x = x_1 →     …
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用引理 `Convexity.StdSimplex.map_sConvexComb`：map_sConvexComb (s : StdSimplex R 
(StdSimplex R I)) (f : I -> J) : s.sConvexComb.map f = (s.map (map f)).sConvexCo
mb
· 使用引理 `Convexity.StdSimplex.map_map`：map_map (f : StdSimplex R M) (g₁ : M -> N)
 (g₂ : N -> P) : (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x))

--- 原说明 ---
Flattening with the inner combination specialized to `convexCombPair`.
-/
lemma iConvexComb_convexCombPair
    (s t : I → R) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) (h : ∀ i, s i + t i = 1)
    (f : StdSimplex R I) (m₁ m₂ : I → M) :
    f.iConvexComb (fun i ↦ convexCombPair (s i) (t i) (hs i) (ht i) (h i) (m₁ i) (m₂ i)) =
    (f.iConvexComb fun i ↦ duple (m₁ i) (m₂ i) (hs i) (ht i) (h i)).sConvexComb := by
  have := iConvexComb_assoc' (I := I) (J := Fin 2) (R := R) (M := M) f
    (fun i ↦ .duple 0 1 (hs i) (ht i) (h i)) (fun i ↦ ![m₁ i, m₂ i])
  simp [iConvexComb, map_sConvexComb, map_map] at this
  simp only [← convexCombPair.eq_def] at this
  simp only [← iConvexComb.eq_def] at this
  simpa [convexCombPair, ← convexCombPair_def]
/-
**Convexity.convexCombPair_iConvexComb_left** 是 Mathlib 中的一个引理，位于命名空间 `Convexity
`。
形式化陈述：convexCombPair_iConvexComb_left (g : StdSimplex R J) (e : J -> M) (m : M) 
: convexCombPair s t hs ht h (g.iConvexComb e) m = (convexCombPair s t hs ht h (
g.map e) (single m)).sConvexComb
参数：g : StdSimplex R J；e : J -> M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.iConvexComb_const`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.StdSimplex.map_const`：map_const (f : StdSimplex R M) (x : N) :
 f.map (fun _ => x) = .single x
· 使用引理 `Convexity.convexCombPair_iConvexComb_iConvexComb`：convexCombPair_iConvex
Comb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂} (g₁ : StdSimplex R J₁) (g₂ : StdS
implex R J₂) (m₁ : J₁ -> M) (m₂ : J₂ -…
-/
lemma convexCombPair_iConvexComb_left (g : StdSimplex R J) (e : J → M) (m : M) :
    convexCombPair s t hs ht h (g.iConvexComb e) m =
      (convexCombPair s t hs ht h (g.map e) (single m)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g e (fun _ ↦ m)
/-
**Convexity.convexCombPair_iConvexComb_right** 是 Mathlib 中的一个引理，位于命名空间 `Convexit
y`。
形式化陈述：convexCombPair_iConvexComb_right (m : M) (g : StdSimplex R J) (e : J -> M)
 : convexCombPair s t hs ht h m (g.iConvexComb e) = (convexCombPair s t hs ht h 
(.single m) (g.map e)).sConvexComb
参数：m : M；g : StdSimplex R J；e : J -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.iConvexComb_const`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.StdSimplex.map_const`：map_const (f : StdSimplex R M) (x : N) :
 f.map (fun _ => x) = .single x
· 使用引理 `Convexity.convexCombPair_iConvexComb_iConvexComb`：convexCombPair_iConvex
Comb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂} (g₁ : StdSimplex R J₁) (g₂ : StdS
implex R J₂) (m₁ : J₁ -> M) (m₂ : J₂ -…
-/
lemma convexCombPair_iConvexComb_right (m : M) (g : StdSimplex R J) (e : J → M) :
    convexCombPair s t hs ht h m (g.iConvexComb e) =
      (convexCombPair s t hs ht h (.single m) (g.map e)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g (fun _ ↦ m) e

/-- Flattening nested binary convex combination into a single convex combination. -/
/-
**Convexity.convexCombPair_convexCombPair_left_eq_sConvexComb** 是 Mathlib 中的一个引理
，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_convexCombPair_left_eq_sConvexComb (m₁ m₂ m₃ : M) : convexC
ombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ = (convexCombPair
 s t hs ht h (duple m₁ m₂ hs' ht' h') (single m₃)).sConvexComb
参数：m₁ m₂ m₃ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.iConvexComb_id'`：∀ {R : Type u_1} {M : Type u_3} [inst : Parti
alOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Co
nvexity.ConvexS…
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用引理 `Convexity.convexCombPair_iConvexComb_left`：convexCombPair_iConvexComb_le
ft (g : StdSimplex R J) (e : J -> M) (m : M) : convexCombPair s t hs ht h (g.iCo
nvexComb e) m = (convexCombPair…

--- 原说明 ---
Flattening nested binary convex combination into a single convex combination.
-/
lemma convexCombPair_convexCombPair_left_eq_sConvexComb (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      (convexCombPair s t hs ht h (duple m₁ m₂ hs' ht' h') (single m₃)).sConvexComb := by
  simpa using! convexCombPair_iConvexComb_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

/-- Flattening nested binary convex combination into a single convex combination. -/
/-
**Convexity.convexCombPair_convexCombPair_right_eq_sConvexComb** 是 Mathlib 中的一个引
理，位于命名空间 `Convexity`。
形式化陈述：convexCombPair_convexCombPair_right_eq_sConvexComb (m₁ m₂ m₃ : M) : convex
CombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) = (convexCombPai
r s t hs ht h (.single m₁) (duple m₂ m₃ hs' ht' h')).sConvexComb
参数：m₁ m₂ m₃ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.iConvexComb_id'`：∀ {R : Type u_1} {M : Type u_3} [inst : Parti
alOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Co
nvexity.ConvexS…
· 使用引理 `Convexity.StdSimplex.map_duple`：map_duple {s t : R} (hs : 0 <= s) (ht : 
0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) : (duple x y hs ht h).map f = dup
le (f x) (f y) hs ht…
· 使用引理 `Convexity.convexCombPair_iConvexComb_right`：convexCombPair_iConvexComb_r
ight (m : M) (g : StdSimplex R J) (e : J -> M) : convexCombPair s t hs ht h m (g
.iConvexComb e) = (convexCombPai…

--- 原说明 ---
Flattening nested binary convex combination into a single convex combination.
-/
lemma convexCombPair_convexCombPair_right_eq_sConvexComb (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      (convexCombPair s t hs ht h (.single m₁) (duple m₂ m₃ hs' ht' h')).sConvexComb := by
  simpa using! convexCombPair_iConvexComb_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id
/-
**Convexity.convexCombPair_convexCombPair_assoc_left** 是 Mathlib 中的一个引理，位于命名空间 `
Convexity`。
形式化陈述：convexCombPair_convexCombPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ 
m₂ m₃ : M) : convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) 
m₃ = convexCombPair (s * s') (s * t' + t) (by positivity) (by positivity) (by rw
 [← add_assoc, ← mul_add, h', mul_one, h]) m₁ (convexCombPair s'' t'' hs'' ht'' 
h'' m₂ m₃)
参数：H : t * s'' = s * t' * t''；m₁ m₂ m₃ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.convexCombPair_convexCombPair_left_eq_sConvexComb`：convexCombP
air_convexCombPair_left_eq_sConvexComb (m₁ m₂ m₃ : M) : convexCombPair s t hs ht
 h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ = (…
· 使用引理 `Convexity.convexCombPair_convexCombPair_right_eq_sConvexComb`：convexComb
Pair_convexCombPair_right_eq_sConvexComb (m₁ m₂ m₃ : M) : convexCombPair s t hs 
ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) = …
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Convexity.StdSimplex.weights_sConvexComb`：∀ {R : Type u_1} {I : Type u_6
} [inst : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]
   (f : Convexity.StdSimplex R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_duple`：∀ {R : Type u} [inst : PartialOrder 
R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x y : 
M)   {s t : R} (hs : 0 ≤…
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Convexity.StdSimplex.weights_single`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x : M
),   (Convexity.StdSimple…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma convexCombPair_convexCombPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      convexCombPair (s * s') (s * t' + t) (by positivity) (by positivity)
        (by rw [← add_assoc, ← mul_add, h', mul_one, h]) m₁
        (convexCombPair s'' t'' hs'' ht'' h'' m₂ m₃) := by
  classical
  rw [convexCombPair_convexCombPair_left_eq_sConvexComb,
    convexCombPair_convexCombPair_right_eq_sConvexComb]
  congr 1
  ext1
  have : s * (t' * t'') + t * t'' = t := by rw [← mul_assoc, ← H, ← mul_add, h'', mul_one]
  simp [convexCombPair, sum_add_index, add_smul, ← single_add, H, mul_assoc, ← mul_add, h'',
    add_assoc, this]
/-
**Convexity.convexCombPair_convexCombPair_assoc_right** 是 Mathlib 中的一个引理，位于命名空间 
`Convexity`。
形式化陈述：convexCombPair_convexCombPair_assoc_right (H : s * t'' = t * s' * s'') (m₁
 m₂ m₃ : M) : convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ 
m₃) = convexCombPair (s + t * s') (t * t') (by positivity) (by positivity) (by r
w [add_assoc, ← mul_add, h', mul_one, h]) (convexCombPair s'' t'' hs'' ht'' h'' 
m₁ m₂) m₃
参数：H : s * t'' = t * s' * s''；m₁ m₂ m₃ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.convexCombPair_symm`：convexCombPair_symm {x y : M} : convexCom
bPair s t hs ht h x y = convexCombPair t s ht hs ((add_comm _ _).trans h) y x
· 使用引理 `Convexity.convexCombPair_convexCombPair_assoc_left`：convexCombPair_conve
xCombPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M) : convexCombPai
r s t hs ht h (convexCombPair s' t' hs' …
-/
lemma convexCombPair_convexCombPair_assoc_right (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      convexCombPair (s + t * s') (t * t') (by positivity) (by positivity)
        (by rw [add_assoc, ← mul_add, h', mul_one, h])
        (convexCombPair s'' t'' hs'' ht'' h'' m₁ m₂) m₃ := by
  simp only [add_comm s]
  rw [convexCombPair_symm, convexCombPair_symm (x := m₂),
    convexCombPair_convexCombPair_assoc_left (hs'' := ht'') (ht'' := hs'')
      (h'' := (add_comm _ _).trans h'') (H := H),
    convexCombPair_symm, convexCombPair_symm (x := m₂)]

section CommSemiring

variable {R M I : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] {s t : R} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)

/-
**Convexity.iConvexComb_convexCombPair_comm** 是 Mathlib 中的一个引理，位于命名空间 `Convexity
`。
形式化陈述：iConvexComb_convexCombPair_comm (f : StdSimplex R I) (e₁ e₂ : I -> M) : f.
iConvexComb (fun x => convexCombPair s t hs ht h (e₁ x) (e₂ x)) = convexCombPair
 s t hs ht h (f.iConvexComb e₁) (f.iConvexComb e₂)
参数：f : StdSimplex R I；e₁ e₂ : I -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.convexCombPair_def`：convexCombPair_def (p q : M) : convexCombP
air s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexComb ![p, q]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Convexity.iConvexComb_comm`：iConvexComb_comm (f : StdSimplex R I) (g : S
tdSimplex R J) (e : I -> J -> M) : f.iConvexComb (fun i => g.iConvexComb (e i)) 
= g.iConvexComb …
-/
lemma iConvexComb_convexCombPair_comm (f : StdSimplex R I) (e₁ e₂ : I → M) :
    f.iConvexComb (fun x ↦ convexCombPair s t hs ht h (e₁ x) (e₂ x)) =
      convexCombPair s t hs ht h (f.iConvexComb e₁) (f.iConvexComb e₂) := by
  simp only [convexCombPair_def]
  convert (iConvexComb_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i _ j _ j
  · fin_cases j <;> simp
  · fin_cases j <;> simp
/-
**Convexity.iConvexComb_convexCombPair_comm_left** 是 Mathlib 中的一个引理，位于命名空间 `Conv
exity`。
形式化陈述：iConvexComb_convexCombPair_comm_left (f : StdSimplex R I) (m : M) (e : I -
> M) : f.iConvexComb (fun x => convexCombPair s t hs ht h (e x) m) = convexCombP
air s t hs ht h (f.iConvexComb e) m
参数：f : StdSimplex R I；m : M；e : I -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.iConvexComb_const`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.iConvexComb_convexCombPair_comm`：iConvexComb_convexCombPair_co
mm (f : StdSimplex R I) (e₁ e₂ : I -> M) : f.iConvexComb (fun x => convexCombPai
r s t hs ht h (e₁ x) (e₂ x)) = …
-/
lemma iConvexComb_convexCombPair_comm_left (f : StdSimplex R I) (m : M) (e : I → M) :
    f.iConvexComb (fun x ↦ convexCombPair s t hs ht h (e x) m) =
    convexCombPair s t hs ht h (f.iConvexComb e) m := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f e (fun _ ↦ m)
/-
**Convexity.iConvexComb_convexCombPair_comm_right** 是 Mathlib 中的一个引理，位于命名空间 `Con
vexity`。
形式化陈述：iConvexComb_convexCombPair_comm_right (f : StdSimplex R I) (m : M) (e : I 
-> M) : f.iConvexComb (convexCombPair s t hs ht h m <| e ·) = convexCombPair s t
 hs ht h m (f.iConvexComb e)
参数：f : StdSimplex R I；m : M；e : I -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.iConvexComb_const`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用引理 `Convexity.iConvexComb_convexCombPair_comm`：iConvexComb_convexCombPair_co
mm (f : StdSimplex R I) (e₁ e₂ : I -> M) : f.iConvexComb (fun x => convexCombPai
r s t hs ht h (e₁ x) (e₂ x)) = …
-/
lemma iConvexComb_convexCombPair_comm_right (f : StdSimplex R I) (m : M) (e : I → M) :
    f.iConvexComb (convexCombPair s t hs ht h m <| e ·) =
    convexCombPair s t hs ht h m (f.iConvexComb e) := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f (fun _ ↦ m) e
/-
**Convexity.isAffineMap_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：isAffineMap_convexCombPair (m : M) : IsAffineMap R (convexCombPair s t hs 
ht h m)
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.iConvexComb_congr`：∀ {R : Type u_1} {M : Type u_3} {I : Type u
_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.iConvexComb_id'`：∀ {R : Type u_1} {M : Type u_3} [inst : Parti
alOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Co
nvexity.ConvexS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.iConvexComb_convexCombPair_comm_right`：iConvexComb_convexCombP
air_comm_right (f : StdSimplex R I) (m : M) (e : I -> M) : f.iConvexComb (convex
CombPair s t hs ht h m <| e ·) = conv…
-/
lemma isAffineMap_convexCombPair (m : M) :
    IsAffineMap R (convexCombPair s t hs ht h m) :=
  ⟨fun f ↦ by simpa using! (iConvexComb_convexCombPair_comm_right hs ht h f m id).symm⟩

end CommSemiring

end Convexity

