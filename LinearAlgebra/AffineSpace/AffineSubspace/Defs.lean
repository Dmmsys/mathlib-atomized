/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Defs

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

* `AffineSubspace k P` is the type of affine subspaces. Unlike affine spaces, affine subspaces are
  allowed to be empty, and lemmas that do not apply to empty affine subspaces have `Nonempty`
  hypotheses. There is a `CompleteLattice` structure on affine subspaces.
* `AffineSubspace.direction` gives the `Submodule` spanned by the pairwise differences of points
  in an `AffineSubspace`. There are various lemmas relating to the set of vectors in the
  `direction`, and relating the lattice structure on affine subspaces to that on their directions.
* `affineSpan` gives the affine subspace spanned by a set of points, with `vectorSpan` giving its
  direction. The `affineSpan` is defined in terms of `spanPoints`, which gives an explicit
  description of the points contained in the affine span; `spanPoints` itself should generally only
  be used when that description is required, with `affineSpan` being the main definition for other
  purposes. Two other descriptions of the affine span are proved equivalent: it is the `sInf` of
  affine subspaces containing the points, and (if `[Nontrivial k]`) it contains exactly those points
  that are affine combinations of points in the given set.

## Implementation notes

`outParam` is used in the definition of `AddTorsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by `P` or
`V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

@[expose] public section
noncomputable section

open Affine

open Set
open scoped Pointwise

section

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

/-- The submodule spanning the differences of a (possibly empty) set of points. -/
/-
**vectorSpan** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：vectorSpan (s : Set P) : Submodule k V
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule spanning the differences of a (possibly empty) set of points.
-/
def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

/-- The definition of `vectorSpan`, for rewriting. -/
/-
**vectorSpan_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s)
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of `vectorSpan`, for rewriting.
-/
theorem vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl

/-- `vectorSpan` is monotone. -/
/-
**vectorSpan_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : vectorSpan k s₁ <= 
vectorSpan k s₂
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.vsub_self_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s
 t : Set β}, s ⊆ t → s -ᵥ s ⊆ t -ᵥ t

--- 原说明 ---
`vectorSpan` is monotone.
-/
theorem vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : vectorSpan k s₁ ≤ vectorSpan k s₂ :=
  Submodule.span_mono (vsub_self_mono h)

variable (P) in
/-- The `vectorSpan` of the empty set is `⊥`. -/
@[simp]
/-
**vectorSpan_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Submodule k V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_def`：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.
span k (s -ᵥ s)
· 使用定理 `Set.vsub_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] (s : S
et β), s -ᵥ ∅ = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥

--- 原说明 ---
The `vectorSpan` of the empty set is `⊥`.
-/
theorem vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Submodule k V) := by
  rw [vectorSpan_def, vsub_empty, Submodule.span_empty]

/-- The `vectorSpan` of a single point is `⊥`. -/
@[simp]
/-
**vectorSpan_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_singleton (p : P) : vectorSpan k ({p} : Set P) = ⊥
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_vsub_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : VS
ub α β] {b c : β}, {b} -ᵥ {c} = {b -ᵥ c}
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `vectorSpan` of a single point is `⊥`.
-/
theorem vectorSpan_singleton (p : P) : vectorSpan k ({p} : Set P) = ⊥ := by simp [vectorSpan_def]

/-- The `s -ᵥ s` lies within the `vectorSpan k s`. -/
/-
**vsub_set_subset_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vsub_set_subset_vectorSpan (s : Set P) : s -ᵥ s subseteq ↑(vectorSpan k s)
参数：s : Set P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
The `s -ᵥ s` lies within the `vectorSpan k s`.
-/
theorem vsub_set_subset_vectorSpan (s : Set P) : s -ᵥ s ⊆ ↑(vectorSpan k s) :=
  Submodule.subset_span

/-- Each pairwise difference is in the `vectorSpan`. -/
/-
**vsub_mem_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s
) : p₁ -ᵥ p₂ in vectorSpan k s
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_set_subset_vectorSpan`：vsub_set_subset_vectorSpan (s : Set P) : s -
ᵥ s subseteq ↑(vectorSpan k s)
· 使用定理 `Set.vsub_mem_vsub`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s 
t : Set β} {b c : β}, b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t

--- 原说明 ---
Each pairwise difference is in the `vectorSpan`.
-/
theorem vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    p₁ -ᵥ p₂ ∈ vectorSpan k s :=
  vsub_set_subset_vectorSpan k s (vsub_mem_vsub hp₁ hp₂)
/-
**vectorSpan_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：vectorSpan_of_subsingleton {s : Set P} (h : s.Subsingleton) : vectorSpan k
 s = ⊥
参数：h : s.Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vectorSpan_empty`：vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Sub
module k V)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
-/
lemma vectorSpan_of_subsingleton {s : Set P} (h : s.Subsingleton) : vectorSpan k s = ⊥ := by
  rcases h.eq_empty_or_singleton with rfl | ⟨p, rfl⟩ <;> simp

@[simp]
/-
**vectorSpan_eq_bot_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：vectorSpan_eq_bot_iff_subsingleton {s : Set P} : vectorSpan k s = ⊥ ↔ s.Su
bsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_subsingleton_iff`：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Non
trivial
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `vectorSpan_of_subsingleton`：vectorSpan_of_subsingleton {s : Set P} (h : 
s.Subsingleton) : vectorSpan k s = ⊥
-/
lemma vectorSpan_eq_bot_iff_subsingleton {s : Set P} : vectorSpan k s = ⊥ ↔ s.Subsingleton := by
  refine ⟨fun h ↦ ?_, vectorSpan_of_subsingleton _⟩
  by_contra hns
  rw [Set.not_subsingleton_iff] at hns
  obtain ⟨p, hp, q, hq, hpq⟩ := hns
  have hpq' := vsub_mem_vectorSpan k hp hq
  simp_all

/-- The points in the affine span of a (possibly empty) set of points. Use `affineSpan` instead to
get an `AffineSubspace k P`. -/
/-
**spanPoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spanPoints (s : Set P) : Set P
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points in the affine span of a (possibly empty) set of points. Use `affineSp
an` instead to
get an `AffineSubspace k P`.
-/
def spanPoints (s : Set P) : Set P :=
  { p | ∃ p₁ ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p₁ }

/-- A point in a set is in its affine span. -/
/-
**mem_spanPoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (p : P) (
s : Set P), p ∈ s → p ∈ spanPoints k s
参数：k : Type u_1；p : P；s : Set P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b

--- 原说明 ---
A point in a set is in its affine span.
-/
theorem mem_spanPoints (p : P) (s : Set P) : p ∈ s → p ∈ spanPoints k s
  | hp => ⟨p, hp, 0, Submodule.zero_mem _, (zero_vadd V p).symm⟩

/-- A set is contained in its `spanPoints`. -/
/-
**subset_spanPoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_spanPoints (s : Set P) : s subseteq spanPoints k s
参数：s : Set P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_spanPoints`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : R
ing k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTor
sor …

--- 原说明 ---
A set is contained in its `spanPoints`.
-/
theorem subset_spanPoints (s : Set P) : s ⊆ spanPoints k s := fun p => mem_spanPoints k p s

/-- The `spanPoints` of a set is nonempty if and only if that set is. -/
@[simp]
/-
**spanPoints_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spanPoints_nonempty (s : Set P) : (spanPoints k s).Nonempty ↔ s.Nonempty
参数：s : Set P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `vectorSpan_empty`：vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Sub
module k V)
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `subset_spanPoints`：subset_spanPoints (s : Set P) : s subseteq spanPoints
 k s

--- 原说明 ---
The `spanPoints` of a set is nonempty if and only if that set is.
-/
theorem spanPoints_nonempty (s : Set P) : (spanPoints k s).Nonempty ↔ s.Nonempty := by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty, Set.not_nonempty_iff_eq_empty]
    intro h
    simp [h, spanPoints]
  · exact fun h => h.mono (subset_spanPoints _ _)

/-- Adding a point in the affine span and a vector in the spanning submodule produces a point in the
affine span. -/
/-
**vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan {s : Set P} {p : P
} {v : V} (hp : p in spanPoints k s) (hv : v in vectorSpan k s) : v +ᵥ p in span
Points k s
参数：hp : p in spanPoints k s；hv : v in vectorSpan k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…

--- 原说明 ---
Adding a point in the affine span and a vector in the spanning submodule produce
s a point in the
affine span.
-/
theorem vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p ∈ spanPoints k s) (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ spanPoints k s := by
  rcases hp with ⟨p₂, ⟨hp₂, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₂p, vadd_vadd]
  exact ⟨p₂, hp₂, v + v₂, (vectorSpan k s).add_mem hv hv₂, rfl⟩

/-- Subtracting two points in the affine span produces a vector in the spanning submodule. -/
/-
**vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints {s : Set P} {p₁ p₂
 : P} (hp₁ : p₁ in spanPoints k s) (hp₂ : p₂ in spanPoints k s) : p₁ -ᵥ p₂ in ve
ctorSpan k s
参数：hp₁ : p₁ in spanPoints k s；hp₂ : p₂ in spanPoints k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s

--- 原说明 ---
Subtracting two points in the affine span produces a vector in the spanning subm
odule.
-/
theorem vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ spanPoints k s) (hp₂ : p₂ ∈ spanPoints k s) : p₁ -ᵥ p₂ ∈ vectorSpan k s := by
  rcases hp₁ with ⟨p₁a, ⟨hp₁a, ⟨v₁, ⟨hv₁, hv₁p⟩⟩⟩⟩
  rcases hp₂ with ⟨p₂a, ⟨hp₂a, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₁p, hv₂p, vsub_vadd_eq_vsub_sub (v₁ +ᵥ p₁a), vadd_vsub_assoc, add_comm, add_sub_assoc]
  have hv₁v₂ : v₁ - v₂ ∈ vectorSpan k s := (vectorSpan k s).sub_mem hv₁ hv₂
  refine (vectorSpan k s).add_mem ?_ hv₁v₂
  exact vsub_mem_vectorSpan k hp₁a hp₂a

end

/-- An `AffineSubspace k P` is a subset of an `AffineSpace V P` that, if not empty, has an affine
space structure induced by a corresponding subspace of the `Module k V`. -/
/-
**AffineSubspace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u_1) →   {V : Type u_2} →     (P : Type u_3) → [inst : Ring k] →
 [inst_1 : AddCommGroup V] → [_root_.Module k V] → [AddTorsor V P] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AffineSubspace k P` is a subset of an `AffineSpace V P` that, if not empty, 
has an affine
space structure induced by a corresponding subspace of the `Module k V`.
-/
structure AffineSubspace (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V]
  [Module k V] [AffineSpace V P] where
  /-- The affine subspace seen as a subset. -/
  carrier : Set P
  protected smul_vsub_vadd_mem' (c : k) {p₁ p₂ p₃ : P} :
    p₁ ∈ carrier → p₂ ∈ carrier → p₃ ∈ carrier → c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ ∈ carrier

namespace AffineSubspace

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (AffineSubspace k P) P where
  coe := carrier
  coe_injective p q _ := by cases p; cases q; congr
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (AffineSubspace k P) := .ofSetLike (AffineSubspace k P) P
/-
**AffineSubspace.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (s : Affi
neSubspace k P), s.carrier = ↑s
参数：s : AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma carrier_eq_coe (s : AffineSubspace k P) : s.carrier = s := rfl
/-
**AffineSubspace.smul_vsub_vadd_mem** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：smul_vsub_vadd_mem (s : AffineSubspace k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in
 s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ in s
参数：s : AffineSubspace k P；c : k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.smul_vsub_vadd_mem'`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
-/
lemma smul_vsub_vadd_mem (s : AffineSubspace k P) (c : k) {p₁ p₂ p₃ : P} :
    p₁ ∈ s → p₂ ∈ s → p₃ ∈ s → c • (p₁ -ᵥ p₂ : V) +ᵥ p₃ ∈ s :=
  s.smul_vsub_vadd_mem' c

/-- A point is in an affine subspace coerced to a set if and only if it is in that affine
subspace. -/
/-
**AffineSubspace.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_coe (p : P) (s : AffineSubspace k P) : p in (s : Set P) ↔ p in s
参数：p : P；s : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point is in an affine subspace coerced to a set if and only if it is in that a
ffine
subspace.
-/
theorem mem_coe (p : P) (s : AffineSubspace k P) : p ∈ (s : Set P) ↔ p ∈ s := by simp

/-- Two affine subspaces are equal if they have the same points. -/
/-
**AffineSubspace.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_injective : Function.Injective ((↑) : AffineSubspace k P -> Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe

--- 原说明 ---
Two affine subspaces are equal if they have the same points.
-/
theorem coe_injective : Function.Injective ((↑) : AffineSubspace k P → Set P) :=
  SetLike.coe_injective

@[ext (iff := false)]
/-
**AffineSubspace.ext** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：ext {p q : AffineSubspace k P} (h : forall x, x in p ↔ x in q) : p = q
参数：h : forall x, x in p ↔ x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {p q : AffineSubspace k P} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
/-
**AffineSubspace.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (s₁ s₂ : 
AffineSubspace k P), s₁ = s₂ ↔ ↑s₁ = ↑s₂
参数：s₁ s₂ : AffineSubspace k P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
protected theorem ext_iff (s₁ s₂ : AffineSubspace k P) : s₁ = s₂ ↔ (s₁ : Set P) = s₂ :=
  SetLike.ext'_iff

end AffineSubspace

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

/-- Reinterprets `p : Submodule k V` as an `AffineSubspace k V`. -/
/-
**Submodule.toAffineSubspace** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     [inst : Ring k] → [inst_1 : AddCom
mGroup V] → [inst_2 : _root_.Module k V] → Submodule k V → AffineSubspace k V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterprets `p : Submodule k V` as an `AffineSubspace k V`.
-/
@[coe] def toAffineSubspace (p : Submodule k V) : AffineSubspace k V where
  carrier := p
  smul_vsub_vadd_mem' _ _ _ _ h₁ h₂ h₃ := p.add_mem (p.smul_mem _ (p.sub_mem h₁ h₂)) h₃
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Submodule k V) (AffineSubspace k V) := ⟨toAffineSubspace⟩

@[simp]
/-
**Submodule.mem_toAffineSubspace** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_toAffineSubspace {p : Submodule k V} {x : V} : x in (p : AffineSubspac
e k V) ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAffineSubspace {p : Submodule k V} {x : V} :
    x ∈ (p : AffineSubspace k V) ↔ x ∈ p := Iff.rfl

end Submodule

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-
**AffineSubspace.vsub_self_of_zero_mem** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace
`。
形式化陈述：vsub_self_of_zero_mem {s : AffineSubspace k V} (hs : 0 in s) : (s : Set V)
 -ᵥ s = s
参数：hs : 0 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vsub_self_of_zero_mem {s : AffineSubspace k V} (hs : 0 ∈ s) :
    (s : Set V) -ᵥ s = s := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using s.smul_vsub_vadd_mem 1 ha hb hs
  · exact fun h => ⟨x, h, 0, hs, by simp⟩
/-
**AffineSubspace.vsub_self_eq_iff_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} [inst : Ring k] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module k V]   {s : AffineSubspace k V} [Nonempty ↥s], ↑s -ᵥ ↑s 
= ↑s ↔ 0 ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_vsub`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s t : S
et β} {a : α}, a ∈ s -ᵥ t ↔ ∃ x ∈ s, ∃ y ∈ t, x -ᵥ y = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AffineSubspace.vsub_self_of_zero_mem`：vsub_self_of_zero_mem {s : AffineS
ubspace k V} (hs : 0 in s) : (s : Set V) -ᵥ s = s
-/
@[simp] lemma vsub_self_eq_iff_zero_mem {s : AffineSubspace k V} [Nonempty s] :
    (s : Set V) -ᵥ s = s ↔ 0 ∈ s := by
  refine ⟨fun h ↦ ?_, vsub_self_of_zero_mem⟩
  obtain x : s := Classical.choice inferInstance
  suffices (x : V) - x ∈ (s : Set _) by aesop
  rw [← h, mem_vsub]
  aesop

/-- The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.)

This can also be used to reinterpret an affine subspace that contains
zero as a submodule, see `direction_eq_self_iff_zero_mem`.
-/
/-
**AffineSubspace.direction** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：direction (s : AffineSubspace k P) : Submodule k V
参数：s : AffineSubspace k P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.)

This can also be used to reinterpret an affine subspace that contains
zero as a submodule, see `direction_eq_self_iff_zero_mem`.
-/
def direction (s : AffineSubspace k P) : Submodule k V :=
  vectorSpan k (s : Set P)

/-- The direction equals the `vectorSpan`. -/
/-
**AffineSubspace.direction_eq_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：direction_eq_vectorSpan (s : AffineSubspace k P) : s.direction = vectorSpa
n k (s : Set P)
参数：s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direction equals the `vectorSpan`.
-/
theorem direction_eq_vectorSpan (s : AffineSubspace k P) : s.direction = vectorSpan k (s : Set P) :=
  rfl

/-- Alternative definition of the direction when the affine subspace is nonempty. This is defined so
that the order on submodules (as used in the definition of `Submodule.span`) can be used in the
proof of `coe_direction_eq_vsub_set`, and is not intended to be used beyond that proof. -/
/-
**AffineSubspace.directionOfNonempty** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：directionOfNonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : 
Submodule k V where carrier
参数：h : (s : Set P).Nonempty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative definition of the direction when the affine subspace is nonempty. Th
is is defined so
that the order on submodules (as used in the definition of `Submodule.span`) can
 be used in the
proof of `coe_direction_eq_vsub_set`, and is not intended to be used beyond that
 proof.
-/
def directionOfNonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : Submodule k V where
  carrier := (s : Set P) -ᵥ s
  zero_mem' := by
    obtain ⟨p, hp⟩ := h
    exact vsub_self p ▸ vsub_mem_vsub hp hp
  add_mem' := by
    rintro _ _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩ ⟨p₃, hp₃, p₄, hp₄, rfl⟩
    rw [← vadd_vsub_assoc]
    refine vsub_mem_vsub ?_ hp₄
    rw [mem_coe]
    convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp₃
    rw [one_smul]
  smul_mem' := by
    rintro c _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    rw [← vadd_vsub (c • (p₁ -ᵥ p₂)) p₂]
    refine vsub_mem_vsub ?_ hp₂
    exact s.smul_vsub_vadd_mem c hp₁ hp₂ hp₂

/-- `direction_of_nonempty` gives the same submodule as `direction`. -/
/-
**AffineSubspace.directionOfNonempty_eq_direction** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineSubspace`。
形式化陈述：directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P)
.Nonempty) : directionOfNonempty h = s.direction
参数：h : (s : Set P).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `AffineSubspace.directionOfNonempty.eq_1`：∀ {k : Type u_1} {V : Type u_2}
 {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modul
e k V]   [inst_3 : AddTorsor …
· 使用定理 `AffineSubspace.direction.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `Submodule.coe_set_mk`：coe_set_mk (S : AddSubmonoid M) (h) : ((⟨S, h⟩ : S
ubmodule R M) : Set M) = S
· 使用定理 `AddSubmonoid.coe_set_mk`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : A
ddSubsemigroup M} (h_zero : 0 ∈ s.carrier),   ↑{ toAddSubsemigroup := s, zero_me
m' := h_zero …
· 使用定理 `vsub_set_subset_vectorSpan`：vsub_set_subset_vectorSpan (s : Set P) : s -
ᵥ s subseteq ↑(vectorSpan k s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
`direction_of_nonempty` gives the same submodule as `direction`.
-/
theorem directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    directionOfNonempty h = s.direction := by
  refine le_antisymm ?_ (Submodule.span_le.2 Set.Subset.rfl)
  rw [← SetLike.coe_subset_coe, directionOfNonempty, direction, Submodule.coe_set_mk,
    AddSubmonoid.coe_set_mk]
  exact vsub_set_subset_vectorSpan k _

/-- The set of vectors in the direction of a nonempty affine subspace is given by `vsub_set`. -/
/-
**AffineSubspace.coe_direction_eq_vsub_set** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonemp
ty) : (s.direction : Set V) = (s : Set P) -ᵥ s
参数：h : (s : Set P).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.directionOfNonempty_eq_direction`：directionOfNonempty_eq_
direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : directionOfNonem
pty h = s.direction

--- 原说明 ---
The set of vectors in the direction of a nonempty affine subspace is given by `v
sub_set`.
-/
theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s :=
  directionOfNonempty_eq_direction h ▸ rfl

/-- A vector is in the direction of a nonempty affine subspace if and only if it is the subtraction
of two vectors in the subspace. -/
/-
**AffineSubspace.mem_direction_iff_eq_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonemp
ty) (v : V) : v in s.direction ↔ exists p₁ in s, exists p₂ in s, v = p₁ -ᵥ p₂
参数：h : (s : Set P).Nonempty；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set`：coe_direction_eq_vsub_set {s :
 AffineSubspace k P} (h : (s : Set P).Nonempty) : (s.direction : Set V) = (s : S
et P) -ᵥ s
· 使用定理 `Set.mem_vsub`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s t : S
et β} {a : α}, a ∈ s -ᵥ t ↔ ∃ x ∈ s, ∃ y ∈ t, x -ᵥ y = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A vector is in the direction of a nonempty affine subspace if and only if it is 
the subtraction
of two vectors in the subspace.
-/
theorem mem_direction_iff_eq_vsub {s : AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) :
    v ∈ s.direction ↔ ∃ p₁ ∈ s, ∃ p₂ ∈ s, v = p₁ -ᵥ p₂ := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set h, Set.mem_vsub]
  simp only [SetLike.mem_coe, eq_comm]

/-- Adding a vector in the direction to a point in the subspace produces a point in the
subspace. -/
/-
**AffineSubspace.vadd_mem_of_mem_direction** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v in s.di
rection) {p : P} (hp : p in s) : v +ᵥ p in s
参数：hv : v in s.direction；hp : p in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_direction_iff_eq_vsub`：mem_direction_iff_eq_vsub {s :
 AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) : v in s.direction ↔ exi
sts p₁ in s, exists p₂ in s, v…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s

--- 原说明 ---
Adding a vector in the direction to a point in the subspace produces a point in 
the
subspace.
-/
theorem vadd_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction) {p : P}
    (hp : p ∈ s) : v +ᵥ p ∈ s := by
  rw [mem_direction_iff_eq_vsub ⟨p, hp⟩] at hv
  rcases hv with ⟨p₁, hp₁, p₂, hp₂, hv⟩
  rw [hv]
  convert s.smul_vsub_vadd_mem 1 hp₁ hp₂ hp
  rw [one_smul]

/-- Subtracting two points in the subspace produces a vector in the direction. -/
/-
**AffineSubspace.vsub_mem_direction** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (h
p₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s

--- 原说明 ---
Subtracting two points in the subspace produces a vector in the direction.
-/
theorem vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    p₁ -ᵥ p₂ ∈ s.direction :=
  vsub_mem_vectorSpan k hp₁ hp₂

/-- Adding a vector to a point in a subspace produces a point in the subspace if and only if the
vector is in the direction. -/
/-
**AffineSubspace.vadd_mem_iff_mem_direction** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : 
p in s) : v +ᵥ p in s ↔ v in s.direction
参数：v : V；hp : p in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s

--- 原说明 ---
Adding a vector to a point in a subspace produces a point in the subspace if and
 only if the
vector is in the direction.
-/
theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s ↔ v ∈ s.direction :=
  ⟨fun h => by simpa using vsub_mem_direction h hp, fun h => vadd_mem_of_mem_direction h hp⟩

/-- Adding a vector in the direction to a point produces a point in the subspace if and only if
the original point is in the subspace. -/
/-
**AffineSubspace.vadd_mem_iff_mem_of_mem_direction** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineSubspace`。
形式化陈述：vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v
 in s.direction) {p : P} : v +ᵥ p in s ↔ p in s
参数：hv : v in s.direction。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vadd_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), -g +ᵥ g +ᵥ a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …

--- 原说明 ---
Adding a vector in the direction to a point produces a point in the subspace if 
and only if
the original point is in the subspace.
-/
theorem vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction)
    {p : P} : v +ᵥ p ∈ s ↔ p ∈ s := by
  refine ⟨fun h => ?_, fun h => vadd_mem_of_mem_direction hv h⟩
  convert! vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

/-- Given a point in an affine subspace, the set of vectors in its direction equals the set of
vectors subtracting that point on the right. -/
/-
**AffineSubspace.coe_direction_eq_vsub_set_right** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSubspace`。
形式化陈述：coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p i
n s) : (s.direction : Set V) = (· -ᵥ p) '' s
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set`：coe_direction_eq_vsub_set {s :
 AffineSubspace k P} (h : (s : Set P).Nonempty) : (s.direction : Set V) = (s : S
et P) -ᵥ s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

--- 原说明 ---
Given a point in an affine subspace, the set of vectors in its direction equals 
the set of
vectors subtracting that point on the right.
-/
theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  rw [coe_direction_eq_vsub_set ⟨p, hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      vadd_mem_of_mem_direction (vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

/-- Given a point in an affine subspace, the set of vectors in its direction equals the set of
vectors subtracting that point on the left. -/
/-
**AffineSubspace.coe_direction_eq_vsub_set_left** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p in
 s) : (s.direction : Set V) = (p -ᵥ ·) '' s
参数：hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set_right`：coe_direction_eq_vsub_se
t_right {s : AffineSubspace k P} {p : P} (hp : p in s) : (s.direction : Set V) =
 (· -ᵥ p) '' s
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given a point in an affine subspace, the set of vectors in its direction equals 
the set of
vectors subtracting that point on the left.
-/
theorem coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (p -ᵥ ·) '' s := by
  ext v
  rw [SetLike.mem_coe, ← Submodule.neg_mem_iff, ← SetLike.mem_coe,
    coe_direction_eq_vsub_set_right hp, Set.mem_image, Set.mem_image]
  conv_lhs =>
    congr
    ext
    rw [← neg_vsub_eq_vsub_rev, neg_inj]

/-- Given a point in an affine subspace, a vector is in its direction if and only if it results from
subtracting that point on the right. -/
/-
**AffineSubspace.mem_direction_iff_eq_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSubspace`。
形式化陈述：mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p i
n s) (v : V) : v in s.direction ↔ exists p₂ in s, v = p₂ -ᵥ p
参数：hp : p in s；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set_right`：coe_direction_eq_vsub_se
t_right {s : AffineSubspace k P} {p : P} (hp : p in s) : (s.direction : Set V) =
 (· -ᵥ p) '' s

--- 原说明 ---
Given a point in an affine subspace, a vector is in its direction if and only if
 it results from
subtracting that point on the right.
-/
theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p₂ -ᵥ p := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

/-- Given a point in an affine subspace, a vector is in its direction if and only if it results from
subtracting that point on the left. -/
/-
**AffineSubspace.mem_direction_iff_eq_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p in
 s) (v : V) : v in s.direction ↔ exists p₂ in s, v = p -ᵥ p₂
参数：hp : p in s；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set_left`：coe_direction_eq_vsub_set
_left {s : AffineSubspace k P} {p : P} (hp : p in s) : (s.direction : Set V) = (
p -ᵥ ·) '' s

--- 原说明 ---
Given a point in an affine subspace, a vector is in its direction if and only if
 it results from
subtracting that point on the left.
-/
theorem mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p -ᵥ p₂ := by
  rw [← SetLike.mem_coe, coe_direction_eq_vsub_set_left hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

/-- An affine subspace contains zero if and only if it equals its directions. -/
/-
**AffineSubspace.direction_eq_self_iff_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} [inst : Ring k] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module k V]   {s : AffineSubspace k V}, ↑s.direction = s ↔ 0 ∈ 
s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `Submodule.mem_toAffineSubspace`：mem_toAffineSubspace {p : Submodule k V}
 {x : V} : x in (p : AffineSubspace k V) ↔ x in p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set`：coe_direction_eq_vsub_set {s :
 AffineSubspace k P} (h : (s : Set P).Nonempty) : (s.direction : Set V) = (s : S
et P) -ᵥ s
· 使用引理 `AffineSubspace.vsub_self_of_zero_mem`：vsub_self_of_zero_mem {s : AffineS
ubspace k V} (hs : 0 in s) : (s : Set V) -ᵥ s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An affine subspace contains zero if and only if it equals its directions.
-/
@[simp] lemma direction_eq_self_iff_zero_mem {s : AffineSubspace k V} :
    s.direction = s ↔ 0 ∈ s where
  mp h := by rw [← h]; simp
  mpr h := by
    ext x
    rw [Submodule.mem_toAffineSubspace, ← SetLike.mem_coe]
    simp [s.coe_direction_eq_vsub_set ⟨0, h⟩, vsub_self_of_zero_mem h]
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (AffineSubspace k V) (Submodule k V) (·) (0 ∈ ·) :=
  ⟨fun _ hs => ⟨_, direction_eq_self_iff_zero_mem.mpr hs⟩⟩

/-- Two affine subspaces with the same direction and nonempty intersection are equal. -/
/-
**AffineSubspace.ext_of_direction_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.d
irection) (hn : ((s₁ : Set P) inter s₂).Nonempty) : s₁ = s₂
参数：hd : s₁.direction = s₂.direction；hn : ((s₁ : Set P) inter s₂).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `Set.mem_of_mem_inter_left`：mem_of_mem_inter_left {x : α} {a b : Set α} (
h : x in a inter b) : x in a
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction

--- 原说明 ---
Two affine subspaces with the same direction and nonempty intersection are equal
.
-/
theorem ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : ((s₁ : Set P) ∩ s₂).Nonempty) : s₁ = s₂ := by
  ext p
  have hq1 := Set.mem_of_mem_inter_left hn.some_mem
  have hq2 := Set.mem_of_mem_inter_right hn.some_mem
  constructor
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq2
    rw [← hd]
    exact vsub_mem_direction hp hq1
  · intro hp
    rw [← vsub_vadd p hn.some]
    refine vadd_mem_of_mem_direction ?_ hq1
    rw [hd]
    exact vsub_mem_direction hp hq2

/-- Two affine subspaces with nonempty intersection are equal if and only if their directions are
equal. -/
/-
**AffineSubspace.eq_iff_direction_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in
 s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction
参数：h₁ : p in s₁；h₂ : p in s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂

--- 原说明 ---
Two affine subspaces with nonempty intersection are equal if and only if their d
irections are
equal.
-/
theorem eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁)
    (h₂ : p ∈ s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction :=
  ⟨fun h => h ▸ rfl, fun h => ext_of_direction_eq h ⟨p, h₁, h₂⟩⟩

/-- Construct an affine subspace from a point and a direction. -/
/-
**AffineSubspace.mk'** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：mk' (p : P) (direction : Submodule k V) : AffineSubspace k P where carrier
参数：p : P；direction : Submodule k V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine subspace from a point and a direction.
-/
def mk' (p : P) (direction : Submodule k V) : AffineSubspace k P where
  carrier := { q | q -ᵥ p ∈ direction }
  smul_vsub_vadd_mem' c p₁ p₂ p₃ hp₁ hp₂ hp₃ := by
    simpa [vadd_vsub_assoc] using
      direction.add_mem (direction.smul_mem c (direction.sub_mem hp₁ hp₂)) hp₃

/-- A point lies in an affine subspace constructed from another point and a direction if and only
if their difference is in that direction. -/
@[simp]
/-
**AffineSubspace.mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_mk' {p q : P} {direction : Submodule k V} : q in mk' p direction ↔ q -
ᵥ p in direction
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point lies in an affine subspace constructed from another point and a directio
n if and only
if their difference is in that direction.
-/
theorem mem_mk' {p q : P} {direction : Submodule k V} : q ∈ mk' p direction ↔ q -ᵥ p ∈ direction :=
  Iff.rfl

/-- An affine subspace constructed from a point and a direction contains that point. -/
/-
**AffineSubspace.self_mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：self_mem_mk' (p : P) (direction : Submodule k V) : p in mk' p direction
参数：p : P；direction : Submodule k V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
An affine subspace constructed from a point and a direction contains that point.
-/
theorem self_mem_mk' (p : P) (direction : Submodule k V) : p ∈ mk' p direction := by
  simp

/-- An affine subspace constructed from a point and a direction contains the result of adding a
vector in that direction to that point. -/
/-
**AffineSubspace.vadd_mem_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：vadd_mem_mk' {v : V} (p : P) {direction : Submodule k V} (hv : v in direct
ion) : v +ᵥ p in mk' p direction
参数：p : P；hv : v in direction。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

--- 原说明 ---
An affine subspace constructed from a point and a direction contains the result 
of adding a
vector in that direction to that point.
-/
theorem vadd_mem_mk' {v : V} (p : P) {direction : Submodule k V} (hv : v ∈ direction) :
    v +ᵥ p ∈ mk' p direction := by
  simpa

/-- An affine subspace constructed from a point and a direction is nonempty. -/
/-
**AffineSubspace.mk'_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (p : P) (
direction : Submodule k V), (↑(AffineSubspace.mk' p direction)).Nonempty
参数：p : P；direction : Submodule k V；↑(AffineSubspace.mk' p direction)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction

--- 原说明 ---
An affine subspace constructed from a point and a direction is nonempty.
-/
theorem mk'_nonempty (p : P) (direction : Submodule k V) : (mk' p direction : Set P).Nonempty :=
  ⟨p, self_mem_mk' p direction⟩
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : P) (direction : Submodule k V) : Nonempty (mk' p direction) :=
  ⟨⟨p, self_mem_mk' p direction⟩⟩

/-- The direction of an affine subspace constructed from a point and a direction. -/
@[simp]
/-
**AffineSubspace.direction_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_mk' (p : P) (direction : Submodule k V) : (mk' p direction).dire
ction = direction
参数：p : P；direction : Submodule k V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_direction_iff_eq_vsub`：mem_direction_iff_eq_vsub {s :
 AffineSubspace k P} (h : (s : Set P).Nonempty) (v : V) : v in s.direction ↔ exi
sts p₁ in s, exists p₂ in s, v…
· 使用定理 `AffineSubspace.mk'_nonempty`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vadd_mem_mk'`：vadd_mem_mk' {v : V} (p : P) {direction : S
ubmodule k V} (hv : v in direction) : v +ᵥ p in mk' p direction
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

--- 原说明 ---
The direction of an affine subspace constructed from a point and a direction.
-/
theorem direction_mk' (p : P) (direction : Submodule k V) :
    (mk' p direction).direction = direction := by
  ext v
  rw [mem_direction_iff_eq_vsub (mk'_nonempty _ _)]
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    simpa using direction.sub_mem hp₁ hp₂
  · exact fun hv => ⟨v +ᵥ p, vadd_mem_mk' _ hv, p, self_mem_mk' _ _, (vadd_vsub _ _).symm⟩

/-- Constructing an affine subspace from a point in a subspace and that subspace's direction
yields the original subspace. -/
@[simp]
/-
**AffineSubspace.mk'_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {s : Affi
neSubspace k P} {p : P}, p ∈ s → AffineSubspace.mk' p s.direction = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction

--- 原说明 ---
Constructing an affine subspace from a point in a subspace and that subspace's d
irection
yields the original subspace.
-/
theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p ∈ s) : mk' p s.direction = s :=
  ext_of_direction_eq (direction_mk' p s.direction) ⟨p, Set.mem_inter (self_mem_mk' _ _) hp⟩

/-- If an affine subspace contains a set of points, it contains the `spanPoints` of that set. -/
/-
**AffineSubspace.spanPoints_subset_coe_of_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `
AffineSubspace`。
形式化陈述：spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} 
(h : s subseteq s₁) : spanPoints k s subseteq s₁
参数：h : s subseteq s₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `vectorSpan_mono`：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
vectorSpan k s₁ <= vectorSpan k s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B

--- 原说明 ---
If an affine subspace contains a set of points, it contains the `spanPoints` of 
that set.
-/
theorem spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    spanPoints k s ⊆ s₁ := by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ ∈ (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s ≤ s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_of_subset hv hs

end AffineSubspace

namespace Submodule

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

@[simp]
/-
**Submodule.toAffineSubspace_direction** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAffineSubspace_direction (s : Submodule k V) : s.toAffineSubspace.direct
ion = s
参数：s : Submodule k V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toAffineSubspace_direction (s : Submodule k V) : s.toAffineSubspace.direction = s := by
  ext x; simp [← s.toAffineSubspace.vadd_mem_iff_mem_direction _ s.zero_mem]

end Submodule

section affineSpan

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-- The affine span of a set of points is the smallest affine subspace containing those points.
(Actually defined here in terms of spans in modules.) -/
/-
**affineSpan** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：affineSpan (s : Set P) : AffineSubspace k P where carrier
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine span of a set of points is the smallest affine subspace containing th
ose points.
(Actually defined here in terms of spans in modules.)
-/
def affineSpan (s : Set P) : AffineSubspace k P where
  carrier := spanPoints k s
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp₃
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂))

/-- The affine span, converted to a set, is `spanPoints`. -/
/-
**coe_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_affineSpan (s : Set P) : (affineSpan k s : Set P) = spanPoints k s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine span, converted to a set, is `spanPoints`.
-/
theorem coe_affineSpan (s : Set P) : (affineSpan k s : Set P) = spanPoints k s :=
  rfl

/-- The condition for a point to be in the affine span, in terms of `vectorSpan`. -/
/-
**mem_affineSpan_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_affineSpan_iff_exists {p : P} {s : Set P} : p in affineSpan k s ↔ exis
ts p₁ in s, exists v in vectorSpan k s, p = v +ᵥ p₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The condition for a point to be in the affine span, in terms of `vectorSpan`.
-/
lemma mem_affineSpan_iff_exists {p : P} {s : Set P} : p ∈ affineSpan k s ↔
    ∃ p₁ ∈ s, ∃ v ∈ vectorSpan k s, p = v +ᵥ p₁ :=
  Iff.rfl

/-- A set is contained in its affine span. -/
/-
**subset_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_affineSpan (s : Set P) : s subseteq affineSpan k s
参数：s : Set P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_spanPoints`：subset_spanPoints (s : Set P) : s subseteq spanPoints
 k s

--- 原说明 ---
A set is contained in its affine span.
-/
theorem subset_affineSpan (s : Set P) : s ⊆ affineSpan k s :=
  subset_spanPoints k s

/-- The direction of the affine span is the `vectorSpan`. -/
/-
**direction_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：direction_affineSpan (s : Set P) : (affineSpan k s).direction = vectorSpan
 k s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `vectorSpan_mono`：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
vectorSpan k s₁ <= vectorSpan k s₂
· 使用定理 `subset_spanPoints`：subset_spanPoints (s : Set P) : s subseteq spanPoints
 k s

--- 原说明 ---
The direction of the affine span is the `vectorSpan`.
-/
theorem direction_affineSpan (s : Set P) : (affineSpan k s).direction = vectorSpan k s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨p₁, ⟨p₂, hp₂, v₁, hv₁, hp₁⟩, p₃, ⟨p₄, hp₄, v₂, hv₂, hp₃⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hp₁, hp₃, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc]
    exact
      (vectorSpan k s).sub_mem ((vectorSpan k s).add_mem hv₁ (vsub_mem_vectorSpan k hp₂ hp₄)) hv₂
  · exact vectorSpan_mono k (subset_spanPoints k s)

/-- A point in a set is in its affine span. -/
/-
**mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in affineSpan k s
参数：hp : p in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_spanPoints`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : R
ing k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTor
sor …

--- 原说明 ---
A point in a set is in its affine span.
-/
theorem mem_affineSpan {p : P} {s : Set P} (hp : p ∈ s) : p ∈ affineSpan k s :=
  mem_spanPoints k p s hp

@[simp]
/-
**vectorSpan_add_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：vectorSpan_add_self (s : Set V) : (vectorSpan k s : Set V) + s = affineSpa
n k s
参数：s : Set V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma vectorSpan_add_self (s : Set V) : (vectorSpan k s : Set V) + s = affineSpan k s := by
  ext
  simp [mem_add, coe_affineSpan, spanPoints]
  grind

variable {k}

/-- Adding a point in the affine span and a vector in the spanning submodule produces a point in the
affine span. -/
/-
**vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan {s : Set P} {p : P
} {v : V} (hp : p in affineSpan k s) (hv : v in vectorSpan k s) : v +ᵥ p in affi
neSpan k s
参数：hp : p in affineSpan k s；hv : v in vectorSpan k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan`：vadd_mem_spanPo
ints_of_mem_spanPoints_of_mem_vectorSpan {s : Set P} {p : P} {v : V} (hp : p in 
spanPoints k s) (hv : v in vectorSpan k s) : …

--- 原说明 ---
Adding a point in the affine span and a vector in the spanning submodule produce
s a point in the
affine span.
-/
theorem vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p ∈ affineSpan k s) (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ affineSpan k s :=
  vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp hv

/-- Subtracting two points in the affine span produces a vector in the spanning submodule. -/
/-
**vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂
 : P} (hp₁ : p₁ in affineSpan k s) (hp₂ : p₂ in affineSpan k s) : p₁ -ᵥ p₂ in ve
ctorSpan k s
参数：hp₁ : p₁ in affineSpan k s；hp₂ : p₂ in affineSpan k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints`：vsub_mem_vector
Span_of_mem_spanPoints_of_mem_spanPoints {s : Set P} {p₁ p₂ : P} (hp₁ : p₁ in sp
anPoints k s) (hp₂ : p₂ in spanPoints k s) : …

--- 原说明 ---
Subtracting two points in the affine span produces a vector in the spanning subm
odule.
-/
theorem vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ affineSpan k s) (hp₂ : p₂ ∈ affineSpan k s) : p₁ -ᵥ p₂ ∈ vectorSpan k s :=
  vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂

/-- If an affine subspace contains a set of points, it contains the affine span of that set. -/
/-
**affineSpan_le_of_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_le_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s s
ubseteq s₁) : affineSpan k s <= s₁
参数：h : s subseteq s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.spanPoints_subset_coe_of_subset_coe`：spanPoints_subset_co
e_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s subseteq s₁) : span
Points k s subseteq s₁

--- 原说明 ---
If an affine subspace contains a set of points, it contains the affine span of t
hat set.
-/
theorem affineSpan_le_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    affineSpan k s ≤ s₁ :=
  AffineSubspace.spanPoints_subset_coe_of_subset_coe h

end affineSpan

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P] {ι : Sort*}

/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (AffineSubspace k P) where
  sup := fun s₁ s₂ => affineSpan k (s₁ ∪ s₂)
  le_sup_left := fun _ _ =>
    Set.Subset.trans Set.subset_union_left (subset_spanPoints k _)
  le_sup_right := fun _ _ =>
    Set.Subset.trans Set.subset_union_right (subset_spanPoints k _)
  sup_le := fun _ _ _ hs₁ hs₂ => spanPoints_subset_coe_of_subset_coe (Set.union_subset hs₁ hs₂)
  inf := fun s₁ s₂ =>
    mk (s₁ ∩ s₂) fun c _ _ _ hp₁ hp₂ hp₃ =>
      ⟨s₁.smul_vsub_vadd_mem c hp₁.1 hp₂.1 hp₃.1, s₂.smul_vsub_vadd_mem c hp₁.2 hp₂.2 hp₃.2⟩
  inf_le_left := fun _ _ => Set.inter_subset_left
  inf_le_right := fun _ _ => Set.inter_subset_right
  top :=
    { carrier := Set.univ
      smul_vsub_vadd_mem' _ _ _ _ _ _ _ := Set.mem_univ _ }
  le_top := fun _ _ _ => Set.mem_univ _
  bot :=
    { carrier := ∅
      smul_vsub_vadd_mem' _ _ _ _ := False.elim }
  bot_le := fun _ _ => False.elim
  sSup := fun s => affineSpan k (⋃ s' ∈ s, (s' : Set P))
  sInf := fun s =>
    mk (⋂ s' ∈ s, (s' : Set P)) fun c p₁ p₂ p₃ hp₁ hp₂ hp₃ =>
      Set.mem_iInter₂.2 fun s₂ hs₂ => by
        rw [Set.mem_iInter₂] at *
        exact s₂.smul_vsub_vadd_mem c (hp₁ s₂ hs₂) (hp₂ s₂ hs₂) (hp₃ s₂ hs₂)
  isLUB_sSup _ :=
    ⟨fun _ h => Set.Subset.trans (Set.subset_biUnion_of_mem h) (subset_spanPoints k _),
      fun _ h => spanPoints_subset_coe_of_subset_coe (Set.iUnion₂_subset h)⟩
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf
  le_inf := fun _ _ _ => Set.subset_inter
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (AffineSubspace k P) :=
  ⟨⊤⟩

/-- The `≤` order on subspaces is the same as that on the corresponding sets. -/
/-
**AffineSubspace.le_def** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：le_def (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ ↔ (s₁ : Set P) subseteq s₂
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `≤` order on subspaces is the same as that on the corresponding sets.
-/
theorem le_def (s₁ s₂ : AffineSubspace k P) : s₁ ≤ s₂ ↔ (s₁ : Set P) ⊆ s₂ :=
  Iff.rfl

/-- One subspace is less than or equal to another if and only if all its points are in the second
subspace. -/
/-
**AffineSubspace.le_def'** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：le_def' (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ ↔ forall p in s₁, p in s₂
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
One subspace is less than or equal to another if and only if all its points are 
in the second
subspace.
-/
theorem le_def' (s₁ s₂ : AffineSubspace k P) : s₁ ≤ s₂ ↔ ∀ p ∈ s₁, p ∈ s₂ :=
  Iff.rfl

/-- The `<` order on subspaces is the same as that on the corresponding sets. -/
/-
**AffineSubspace.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：lt_def (s₁ s₂ : AffineSubspace k P) : s₁ < s₂ ↔ (s₁ : Set P) ⊂ s₂
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `<` order on subspaces is the same as that on the corresponding sets.
-/
theorem lt_def (s₁ s₂ : AffineSubspace k P) : s₁ < s₂ ↔ (s₁ : Set P) ⊂ s₂ :=
  Iff.rfl

/-- One subspace is not less than or equal to another if and only if it has a point not in the
second subspace. -/
/-
**AffineSubspace.not_le_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：not_le_iff_exists (s₁ s₂ : AffineSubspace k P) : ¬s₁ <= s₂ ↔ exists p in s
₁, p ∉ s₂
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t

--- 原说明 ---
One subspace is not less than or equal to another if and only if it has a point 
not in the
second subspace.
-/
theorem not_le_iff_exists (s₁ s₂ : AffineSubspace k P) : ¬s₁ ≤ s₂ ↔ ∃ p ∈ s₁, p ∉ s₂ :=
  Set.not_subset

/-- If a subspace is less than another, there is a point only in the second. -/
/-
**AffineSubspace.exists_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：exists_of_lt {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂) : exists p in s₂, 
p ∉ s₁
参数：h : s₁ < s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s

--- 原说明 ---
If a subspace is less than another, there is a point only in the second.
-/
theorem exists_of_lt {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂) : ∃ p ∈ s₂, p ∉ s₁ :=
  Set.exists_of_ssubset h

/-- A subspace is less than another if and only if it is less than or equal to the second subspace
and there is a point only in the second. -/
/-
**AffineSubspace.lt_iff_le_and_exists** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
形式化陈述：lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) : s₁ < s₂ ↔ s₁ <= s₂ ∧ e
xists p in s₂, p ∉ s₁
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `AffineSubspace.not_le_iff_exists`：not_le_iff_exists (s₁ s₂ : AffineSubsp
ace k P) : ¬s₁ <= s₂ ↔ exists p in s₁, p ∉ s₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subspace is less than another if and only if it is less than or equal to the s
econd subspace
and there is a point only in the second.
-/
theorem lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) :
    s₁ < s₂ ↔ s₁ ≤ s₂ ∧ ∃ p ∈ s₂, p ∉ s₁ := by
  rw [lt_iff_le_not_ge, not_le_iff_exists]

/-- If an affine subspace is nonempty and contained in another with the same direction, they are
equal. -/
/-
**AffineSubspace.eq_of_direction_eq_of_nonempty_of_le** 是 Mathlib 中的一个定理，位于命名空间 
`AffineSubspace`。
形式化陈述：eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P} (hd : s₁
.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ <= s₂) : s₁ = 
s₂
参数：hd : s₁.direction = s₂.direction；hn : (s₁ : Set P).Nonempty；hle : s₁ <= s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂

--- 原说明 ---
If an affine subspace is nonempty and contained in another with the same directi
on, they are
equal.
-/
theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P}
    (hd : s₁.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ ≤ s₂) : s₁ = s₂ :=
  let ⟨p, hp⟩ := hn
  ext_of_direction_eq hd ⟨p, hp, hle hp⟩
/-
**AffineSubspace.nonempty_sup_left** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
形式化陈述：nonempty_sup_left (s₁ s₂ : AffineSubspace k P) [Nonempty s₁] : Nonempty (s
₁ ⊔ s₂ : AffineSubspace k P)
参数：s₁ s₂ : AffineSubspace k P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
instance nonempty_sup_left (s₁ s₂ : AffineSubspace k P) [Nonempty s₁] :
    Nonempty (s₁ ⊔ s₂ : AffineSubspace k P) :=
  .map (Set.inclusion <| SetLike.le_def.1 le_sup_left) ‹_›
/-
**AffineSubspace.nonempty_sup_right** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
形式化陈述：nonempty_sup_right (s₁ s₂ : AffineSubspace k P) [Nonempty s₂] : Nonempty (
s₁ ⊔ s₂ : AffineSubspace k P)
参数：s₁ s₂ : AffineSubspace k P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
instance nonempty_sup_right (s₁ s₂ : AffineSubspace k P) [Nonempty s₂] :
    Nonempty (s₁ ⊔ s₂ : AffineSubspace k P) :=
  .map (Set.inclusion <| SetLike.le_def.1 le_sup_right) ‹_›

variable (k V)

/-- The affine span is the `sInf` of subspaces containing the given points. -/
/-
**AffineSubspace.affineSpan_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_eq_sInf (s : Set P) : affineSpan k s = sInf { s' : AffineSubspa
ce k P | s subseteq s' }
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `affineSpan_le_of_subset_coe`：affineSpan_le_of_subset_coe {s : Set P} {s₁
 : AffineSubspace k P} (h : s subseteq s₁) : affineSpan k s <= s₁
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `subset_spanPoints`：subset_spanPoints (s : Set P) : s subseteq spanPoints
 k s

--- 原说明 ---
The affine span is the `sInf` of subspaces containing the given points.
-/
theorem affineSpan_eq_sInf (s : Set P) :
    affineSpan k s = sInf { s' : AffineSubspace k P | s ⊆ s' } :=
  le_antisymm (affineSpan_le_of_subset_coe <| Set.subset_iInter₂ fun _ => id)
    (sInf_le (subset_spanPoints k _))

variable (P)

/-- The Galois insertion formed by `affineSpan` and coercion back to a set. -/
/-
**AffineSubspace.gi** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：(k : Type u_1) →   (V : Type u_2) →     (P : Type u_3) →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] → [S : AddTorsor V P] → GaloisInsertion (affineSpan k) SetLike.coe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois insertion formed by `affineSpan` and coercion back to a set.
-/
protected def gi : GaloisInsertion (affineSpan k) ((↑) : AffineSubspace k P → Set P) where
  choice s _ := affineSpan k s
  gc s₁ _s₂ :=
    ⟨fun h => Set.Subset.trans (subset_spanPoints k s₁) h, affineSpan_le_of_subset_coe⟩
  le_l_u _ := subset_spanPoints k _
  choice_eq _ _ := rfl

/-- The span of the empty set is `⊥`. -/
@[simp]
/-
**AffineSubspace.span_empty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：span_empty : affineSpan k (∅ : Set P) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The span of the empty set is `⊥`.
-/
theorem span_empty : affineSpan k (∅ : Set P) = ⊥ :=
  (AffineSubspace.gi k V P).gc.l_bot

/-- The span of `univ` is `⊤`. -/
@[simp]
/-
**AffineSubspace.span_univ** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：span_univ : affineSpan k (Set.univ : Set P) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s

--- 原说明 ---
The span of `univ` is `⊤`.
-/
theorem span_univ : affineSpan k (Set.univ : Set P) = ⊤ :=
  eq_top_iff.2 <| subset_affineSpan k _

variable {k V P}
/-
**AffineSubspace._root_.affineSpan_le** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.affineSpan_le {s : Set P} {Q : AffineSubspace k P} :
    affineSpan k s ≤ Q ↔ s ⊆ (Q : Set P) :=
  (AffineSubspace.gi k V P).gc _ _

variable (k V) {p₁ p₂ : P}

/-- The span of a union of sets is the sup of their spans. -/
/-
**AffineSubspace.span_union** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：span_union (s t : Set P) : affineSpan k (s union t) = affineSpan k s ⊔ aff
ineSpan k t
参数：s t : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The span of a union of sets is the sup of their spans.
-/
theorem span_union (s t : Set P) : affineSpan k (s ∪ t) = affineSpan k s ⊔ affineSpan k t :=
  (AffineSubspace.gi k V P).gc.l_sup

/-- The span of a union of an indexed family of sets is the sup of their spans. -/
/-
**AffineSubspace.span_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：span_iUnion {ι : Type*} (s : ι -> Set P) : affineSpan k (⋃ i, s i) = ⨆ i, 
affineSpan k (s i)
参数：s : ι -> Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The span of a union of an indexed family of sets is the sup of their spans.
-/
theorem span_iUnion {ι : Type*} (s : ι → Set P) :
    affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) :=
  (AffineSubspace.gi k V P).gc.l_iSup

variable (P) in
/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp]
/-
**AffineSubspace.top_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：top_coe : ((⊤ : AffineSubspace k P) : Set P) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⊤`, coerced to a set, is the whole set of points.
-/
theorem top_coe : ((⊤ : AffineSubspace k P) : Set P) = Set.univ :=
  rfl

/-- All points are in `⊤`. -/
@[simp]
/-
**AffineSubspace.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
All points are in `⊤`.
-/
theorem mem_top (p : P) : p ∈ (⊤ : AffineSubspace k P) :=
  Set.mem_univ p
/-
**AffineSubspace.mk'_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ (k : Type u_1) (V : Type u_2) {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V P] (p : P), Affin
eSubspace.mk' p ⊤ = ⊤
参数：k : Type u_1；V : Type u_2；p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mk'_top (p : P) : mk' p (⊤ : Submodule k V) = ⊤ := by
  ext x
  simp [mem_mk']

variable (P)

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp]
/-
**AffineSubspace.direction_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_top : (⊤ : AffineSubspace k P).direction = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `imp_intro`：∀ {α β : Prop}, α → β → α
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

--- 原说明 ---
The direction of `⊤` is the whole module as a submodule.
-/
theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  obtain ⟨p⟩ := S.nonempty
  ext v
  refine ⟨imp_intro Submodule.mem_top, fun _hv => ?_⟩
  have hpv : ((v +ᵥ p) -ᵥ p : V) ∈ (⊤ : AffineSubspace k P).direction :=
    vsub_mem_direction (mem_top k V _) (mem_top k V _)
  rwa [vadd_vsub] at hpv

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp]
/-
**AffineSubspace.bot_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⊥`, coerced to a set, is the empty set.
-/
theorem bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅ :=
  rfl
/-
**AffineSubspace.bot_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：bot_ne_top : (⊥ : AffineSubspace k P) != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_ne_univ`：empty_ne_univ [Nonempty α] : (∅ : Set α) != univ
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.top_coe`：top_coe : ((⊤ : AffineSubspace k P) : Set P) = S
et.univ
· 使用定理 `AffineSubspace.bot_coe`：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
· 使用定理 `AffineSubspace.ext_iff`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [
inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 
: AddTorsor …
-/
theorem bot_ne_top : (⊥ : AffineSubspace k P) ≠ ⊤ := by
  intro contra
  rw [AffineSubspace.ext_iff, bot_coe, top_coe] at contra
  exact Set.empty_ne_univ contra
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (AffineSubspace k P) :=
  ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩
/-
**AffineSubspace.nonempty_of_affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Non
empty
参数：h : affineSpan k s = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `AffineSubspace.bot_ne_top`：bot_ne_top : (⊥ : AffineSubspace k P) != ⊤
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact bot_ne_top k V P h

/-- If the affine span of a set is `⊤`, then the vector span of the same set is the `⊤`. -/
/-
**AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空
间 `AffineSubspace`。
形式化陈述：vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤
) : vectorSpan k s = ⊤
参数：h : affineSpan k s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤

--- 原说明 ---
If the affine span of a set is `⊤`, then the vector span of the same set is the 
`⊤`.
-/
theorem vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) :
    vectorSpan k s = ⊤ := by rw [← direction_affineSpan, h, direction_top]

/-- For a nonempty set, the affine span is `⊤` iff its vector span is `⊤`. -/
/-
**AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty** 是 Mathlib
 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.No
nempty) : affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top`：vectorSpan_eq_top
_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : vectorSpan k s = ⊤
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.eq_iff_direction_eq_of_mem`：eq_iff_direction_eq_of_mem {s
₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.
direction = s₂.direction
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤

--- 原说明 ---
For a nonempty set, the affine span is `⊤` iff its vector span is `⊤`.
-/
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  refine ⟨vectorSpan_eq_top_of_affineSpan_eq_top k V P, ?_⟩
  intro h
  suffices Nonempty (affineSpan k s) by
    obtain ⟨p, hp : p ∈ affineSpan k s⟩ := this
    rw [eq_iff_direction_eq_of_mem hp (mem_top k V p), direction_affineSpan, h, direction_top]
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨x, mem_affineSpan k hx⟩⟩

/-- For a non-trivial space, the affine span of a set is `⊤` iff its vector span is `⊤`. -/
/-
**AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial** 是 Mathl
ib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial {s : Set P} [Nontriv
ial P] : affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `AffineSubspace.instNontrivial`：∀ (k : Type u_1) (V : Type u_2) (P : Type
 u_3) [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
S : AddTorsor V P],…
· 使用定理 `vectorSpan_empty`：vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Sub
module k V)
· 使用定理 `AddTorsor.subsingleton_iff`：∀ (G : Type u_1) (P : Type u_2) [inst : AddG
roup G] [AddTorsor G P], Subsingleton G ↔ Subsingleton P
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty`：affi
neSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty {s : Set P} (hs : s.Nonempty) : 
affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
For a non-trivial space, the affine span of a set is `⊤` iff its vector span is 
`⊤`.
-/
theorem affineSpan_eq_top_iff_vectorSpan_eq_top_of_nontrivial {s : Set P} [Nontrivial P] :
    affineSpan k s = ⊤ ↔ vectorSpan k s = ⊤ := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, subsingleton_iff_bot_eq_top, AddTorsor.subsingleton_iff V P, not_subsingleton]
  · rw [affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty k V P hs]
/-
**AffineSubspace.card_pos_of_affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：card_pos_of_affineSpan_eq_top {ι : Type*} [Fintype ι] {p : ι -> P} (h : af
fineSpan k (range p) = ⊤) : 0 < Fintype.card ι
参数：h : affineSpan k (range p) = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.nonempty_of_affineSpan_eq_top`：nonempty_of_affineSpan_eq_
top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
-/
theorem card_pos_of_affineSpan_eq_top {ι : Type*} [Fintype ι] {p : ι → P}
    (h : affineSpan k (range p) = ⊤) : 0 < Fintype.card ι := by
  obtain ⟨-, ⟨i, -⟩⟩ := nonempty_of_affineSpan_eq_top k V P h
  exact Fintype.card_pos_iff.mpr ⟨i⟩

-- An instance with better keys for the context
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (⊤ : AffineSubspace k P) := inferInstanceAs (Nonempty (⊤ : Set P))

variable {P}

/-- No points are in `⊥`. -/
/-
**AffineSubspace.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：notMem_bot (p : P) : p ∉ (⊥ : AffineSubspace k P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)

--- 原说明 ---
No points are in `⊥`.
-/
theorem notMem_bot (p : P) : p ∉ (⊥ : AffineSubspace k P) :=
  Set.notMem_empty p
/-
**AffineSubspace.isEmpty_bot** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
形式化陈述：isEmpty_bot : IsEmpty (⊥ : AffineSubspace k P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.isEmpty_of_false`：Subtype.isEmpty_of_false {p : α -> Prop} (hp :
 forall a, ¬p a) : IsEmpty (Subtype p)
· 使用定理 `AffineSubspace.notMem_bot`：notMem_bot (p : P) : p ∉ (⊥ : AffineSubspace 
k P)
-/
instance isEmpty_bot : IsEmpty (⊥ : AffineSubspace k P) :=
  Subtype.isEmpty_of_false fun _ ↦ notMem_bot _ _ _

variable (P)

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp]
/-
**AffineSubspace.direction_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_bot : (⊥ : AffineSubspace k P).direction = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.direction_eq_vectorSpan`：direction_eq_vectorSpan (s : Aff
ineSubspace k P) : s.direction = vectorSpan k (s : Set P)
· 使用定理 `AffineSubspace.bot_coe`：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
· 使用定理 `vectorSpan_def`：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.
span k (s -ᵥ s)
· 使用定理 `Set.vsub_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] (s : S
et β), s -ᵥ ∅ = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥

--- 原说明 ---
The direction of `⊥` is the submodule `⊥`.
-/
theorem direction_bot : (⊥ : AffineSubspace k P).direction = ⊥ := by
  rw [direction_eq_vectorSpan, bot_coe, vectorSpan_def, vsub_empty, Submodule.span_empty]

variable {k V P}

@[simp]
/-
**AffineSubspace.coe_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥
参数：Q : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `AffineSubspace.bot_coe`：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
-/
theorem coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥ :=
  coe_injective.eq_iff' (bot_coe _ _ _)

@[simp]
/-
**AffineSubspace.coe_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = univ ↔ Q = ⊤
参数：Q : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `AffineSubspace.coe_injective`：coe_injective : Function.Injective ((↑) : 
AffineSubspace k P -> Set P)
· 使用定理 `AffineSubspace.top_coe`：top_coe : ((⊤ : AffineSubspace k P) : Set P) = S
et.univ
-/
theorem coe_eq_univ_iff (Q : AffineSubspace k P) : (Q : Set P) = univ ↔ Q = ⊤ :=
  coe_injective.eq_iff' (top_coe _ _ _)
/-
**AffineSubspace.nonempty_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：nonempty_iff_ne_bot (Q : AffineSubspace k P) : (Q : Set P).Nonempty ↔ Q !=
 ⊥
参数：Q : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
-/
theorem nonempty_iff_ne_bot (Q : AffineSubspace k P) : (Q : Set P).Nonempty ↔ Q ≠ ⊥ := by
  rw [nonempty_iff_ne_empty]
  exact not_congr Q.coe_eq_bot_iff
/-
**AffineSubspace.eq_bot_or_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
参数：Q : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.nonempty_iff_ne_bot`：nonempty_iff_ne_bot (Q : AffineSubsp
ace k P) : (Q : Set P).Nonempty ↔ Q != ⊥
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
-/
theorem eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty := by
  rw [nonempty_iff_ne_bot]
  apply eq_or_ne
/-
**AffineSubspace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSubspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton P] : IsSimpleOrder (AffineSubspace k P) where
  eq_bot_or_eq_top (s : AffineSubspace k P) := by
    rw [← coe_eq_bot_iff, ← coe_eq_univ_iff]
    rcases (s : Set P).eq_empty_or_nonempty with h | h
    · exact .inl h
    · exact .inr h.eq_univ

/-- A nonempty affine subspace is `⊤` if and only if its direction is `⊤`. -/
@[simp]
/-
**AffineSubspace.direction_eq_top_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineSubspace`。
形式化陈述：direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P)
.Nonempty) : s.direction = ⊤ ↔ s = ⊤
参数：h : (s : Set P).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A nonempty affine subspace is `⊤` if and only if its direction is `⊤`.
-/
theorem direction_eq_top_iff_of_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    s.direction = ⊤ ↔ s = ⊤ := by
  constructor
  · intro hd
    rw [← direction_top k V P] at hd
    refine ext_of_direction_eq hd ?_
    simp [h]
  · rintro rfl
    simp

/-- The inf of two affine subspaces, coerced to a set, is the intersection of the two sets of
points. -/
@[simp]
/-
**AffineSubspace.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_inf (s₁ s₂ : AffineSubspace k P) : (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) in
ter s₂
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two affine subspaces, coerced to a set, is the intersection of the tw
o sets of
points.
-/
theorem coe_inf (s₁ s₂ : AffineSubspace k P) : (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) ∩ s₂ :=
  rfl

/-- A point is in the inf of two affine subspaces if and only if it is in both of them. -/
/-
**AffineSubspace.mem_inf_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace k P) : p in s₁ ⊓ s₂ ↔ p in s₁ 
∧ p in s₂
参数：p : P；s₁ s₂ : AffineSubspace k P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point is in the inf of two affine subspaces if and only if it is in both of th
em.
-/
theorem mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace k P) : p ∈ s₁ ⊓ s₂ ↔ p ∈ s₁ ∧ p ∈ s₂ :=
  Iff.rfl

/-- The direction of the inf of two affine subspaces is less than or equal to the inf of their
directions. -/
/-
**AffineSubspace.direction_inf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_inf (s₁ s₂ : AffineSubspace k P) : (s₁ ⊓ s₂).direction <= s₁.dir
ection ⊓ s₂.direction
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Set.vsub_self_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s
 t : Set β}, s ⊆ t → s -ᵥ s ⊆ t -ᵥ t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The direction of the inf of two affine subspaces is less than or equal to the in
f of their
directions.
-/
theorem direction_inf (s₁ s₂ : AffineSubspace k P) :
    (s₁ ⊓ s₂).direction ≤ s₁.direction ⊓ s₂.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    le_inf (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_left) hp)
      (sInf_le_sInf fun p hp => trans (vsub_self_mono inter_subset_right) hp)

/-- If two affine subspaces have a point in common, the direction of their inf equals the inf of
their directions. -/
/-
**AffineSubspace.direction_inf_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`
。
形式化陈述：direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (
h₂ : p in s₂) : (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction
参数：h₁ : p in s₁；h₂ : p in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.mem_inf_iff`：mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace 
k P) : p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If two affine subspaces have a point in common, the direction of their inf equal
s the inf of
their directions.
-/
theorem direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := by
  ext v
  rw [Submodule.mem_inf, ← vadd_mem_iff_mem_direction v h₁, ← vadd_mem_iff_mem_direction v h₂, ←
    vadd_mem_iff_mem_direction v ((mem_inf_iff p s₁ s₂).2 ⟨h₁, h₂⟩), mem_inf_iff]

/-- If two affine subspaces have a point in their inf, the direction of their inf equals the inf of
their directions. -/
/-
**AffineSubspace.direction_inf_of_mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p in s₁
 ⊓ s₂) : (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction
参数：h : p in s₁ ⊓ s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.direction_inf_of_mem`：direction_inf_of_mem {s₁ s₂ : Affin
eSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : (s₁ ⊓ s₂).direction = s₁.
direction ⊓ s₂.direction
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.mem_inf_iff`：mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace 
k P) : p in s₁ ⊓ s₂ ↔ p in s₁ ∧ p in s₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If two affine subspaces have a point in their inf, the direction of their inf eq
uals the inf of
their directions.
-/
theorem direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction :=
  direction_inf_of_mem ((mem_inf_iff p s₁ s₂).1 h).1 ((mem_inf_iff p s₁ s₂).1 h).2

@[simp, norm_cast]
/-
**AffineSubspace.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_sInf (t : Set (AffineSubspace k P)) : ((sInf t : AffineSubspace k P) :
 Set P) = ⋂ s in t, s
参数：t : Set (AffineSubspace k P)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (t : Set (AffineSubspace k P)) :
    ((sInf t : AffineSubspace k P) : Set P) = ⋂ s ∈ t, s :=
  rfl
/-
**AffineSubspace.mem_sInf_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_sInf_iff (p : P) (t : Set (AffineSubspace k P)) : p in sInf t ↔ forall
 s in t, p in s
参数：p : P；t : Set (AffineSubspace k P)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf_iff (p : P) (t : Set (AffineSubspace k P)) : p ∈ sInf t ↔ ∀ s ∈ t, p ∈ s :=
  Set.mem_iInter₂
/-
**AffineSubspace.direction_sInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_sInf (t : Set (AffineSubspace k P)) : direction (sInf t) <= ⨅ s 
in t, s.direction
参数：t : Set (AffineSubspace k P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.vsub_self_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s
 t : Set β}, s ⊆ t → s -ᵥ s ⊆ t -ᵥ t
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
-/
theorem direction_sInf (t : Set (AffineSubspace k P)) :
    direction (sInf t) ≤ ⨅ s ∈ t, s.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact le_iInf₂ fun s hs => Submodule.span_mono <| vsub_self_mono <| biInter_subset_of_mem hs
/-
**AffineSubspace.direction_sInf_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：direction_sInf_of_mem (t : Set (AffineSubspace k P)) (p : P) (h : forall s
 in t, p in s) : direction (sInf t) = ⨅ s in t, s.direction
参数：t : Set (AffineSubspace k P)；p : P；h : forall s in t, p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `AffineSubspace.direction_sInf`：direction_sInf (t : Set (AffineSubspace k
 P)) : direction (sInf t) <= ⨅ s in t, s.direction
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.mem_sInf_iff`：mem_sInf_iff (p : P) (t : Set (AffineSubspa
ce k P)) : p in sInf t ↔ forall s in t, p in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem direction_sInf_of_mem (t : Set (AffineSubspace k P)) (p : P) (h : ∀ s ∈ t, p ∈ s) :
    direction (sInf t) = ⨅ s ∈ t, s.direction := by
  apply (direction_sInf t).antisymm
  intro v hv
  rw [← vadd_mem_iff_mem_direction v ((mem_sInf_iff p t).mpr h), mem_sInf_iff]
  intro s hs
  rw [vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs
/-
**AffineSubspace.direction_sInf_of_mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：direction_sInf_of_mem_sInf (t : Set (AffineSubspace k P)) (p : P) (h : p i
n sInf t) : direction (sInf t) = ⨅ s in t, s.direction
参数：t : Set (AffineSubspace k P)；p : P；h : p in sInf t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.direction_sInf_of_mem`：direction_sInf_of_mem (t : Set (Af
fineSubspace k P)) (p : P) (h : forall s in t, p in s) : direction (sInf t) = ⨅ 
s in t, s.direction
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.mem_sInf_iff`：mem_sInf_iff (p : P) (t : Set (AffineSubspa
ce k P)) : p in sInf t ↔ forall s in t, p in s
-/
theorem direction_sInf_of_mem_sInf (t : Set (AffineSubspace k P)) (p : P) (h : p ∈ sInf t) :
    direction (sInf t) = ⨅ s ∈ t, s.direction :=
  direction_sInf_of_mem t p <| (mem_sInf_iff p t).mp h

@[simp, norm_cast]
/-
**AffineSubspace.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_iInf (s : ι -> AffineSubspace k P) : ((iInf s : AffineSubspace k P) : 
Set P) = ⋂ i, s i
参数：s : ι -> AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `AffineSubspace.coe_sInf`：coe_sInf (t : Set (AffineSubspace k P)) : ((sIn
f t : AffineSubspace k P) : Set P) = ⋂ s in t, s
· 使用定理 `Set.biInter_range`：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in 
range f, g x = ⋂ y, g (f y)
-/
theorem coe_iInf (s : ι → AffineSubspace k P) :
    ((iInf s : AffineSubspace k P) : Set P) = ⋂ i, s i := by
  rw [iInf, coe_sInf, Set.biInter_range]
/-
**AffineSubspace.mem_iInf_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_iInf_iff (s : ι -> AffineSubspace k P) (p : P) : p in iInf s ↔ forall 
i, p in s i
参数：s : ι -> AffineSubspace k P；p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `AffineSubspace.mem_sInf_iff`：mem_sInf_iff (p : P) (t : Set (AffineSubspa
ce k P)) : p in sInf t ↔ forall s in t, p in s
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iInf_iff (s : ι → AffineSubspace k P) (p : P) : p ∈ iInf s ↔ ∀ i, p ∈ s i := by
  rw [iInf, mem_sInf_iff, Set.forall_mem_range]
/-
**AffineSubspace.direction_iInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_iInf (s : ι -> AffineSubspace k P) : (iInf s).direction <= ⨅ i, 
(s i).direction
参数：s : ι -> AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `AffineSubspace.direction_sInf`：direction_sInf (t : Set (AffineSubspace k
 P)) : direction (sInf t) <= ⨅ s in t, s.direction
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem direction_iInf (s : ι → AffineSubspace k P) :
    (iInf s).direction ≤ ⨅ i, (s i).direction := by
  apply (direction_sInf _).trans_eq
  rw [iInf_range]
/-
**AffineSubspace.direction_iInf_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：direction_iInf_of_mem (s : ι -> AffineSubspace k P) (p : P) (h : forall i,
 p in s i) : (iInf s).direction = ⨅ i, (s i).direction
参数：s : ι -> AffineSubspace k P；p : P；h : forall i, p in s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `AffineSubspace.direction_sInf_of_mem`：direction_sInf_of_mem (t : Set (Af
fineSubspace k P)) (p : P) (h : forall s in t, p in s) : direction (sInf t) = ⨅ 
s in t, s.direction
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem direction_iInf_of_mem (s : ι → AffineSubspace k P) (p : P) (h : ∀ i, p ∈ s i) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, direction_sInf_of_mem _ p ?_, iInf_range]
  rwa [Set.forall_mem_range]
/-
**AffineSubspace.direction_iInf_of_mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：direction_iInf_of_mem_iInf (s : ι -> AffineSubspace k P) (p : P) (h : p in
 iInf s) : (iInf s).direction = ⨅ i, (s i).direction
参数：s : ι -> AffineSubspace k P；p : P；h : p in iInf s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `AffineSubspace.direction_sInf_of_mem_sInf`：direction_sInf_of_mem_sInf (t
 : Set (AffineSubspace k P)) (p : P) (h : p in sInf t) : direction (sInf t) = ⨅ 
s in t, s.direction
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem direction_iInf_of_mem_iInf (s : ι → AffineSubspace k P) (p : P) (h : p ∈ iInf s) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  rw [iInf, direction_sInf_of_mem_sInf _ p h, iInf_range]

/-- If one affine subspace is less than or equal to another, the same applies to their
directions. -/
/-
**AffineSubspace.direction_le** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_le {s₁ s₂ : AffineSubspace k P} (h : s₁ <= s₂) : s₁.direction <=
 s₂.direction
参数：h : s₁ <= s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vectorSpan_mono`：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
vectorSpan k s₁ <= vectorSpan k s₂

--- 原说明 ---
If one affine subspace is less than or equal to another, the same applies to the
ir
directions.
-/
theorem direction_le {s₁ s₂ : AffineSubspace k P} (h : s₁ ≤ s₂) : s₁.direction ≤ s₂.direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

/-- The sup of the directions of two affine subspaces is less than or equal to the direction of
their sup. -/
/-
**AffineSubspace.sup_direction_le** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：sup_direction_le (s₁ s₂ : AffineSubspace k P) : s₁.direction ⊔ s₂.directio
n <= (s₁ ⊔ s₂).direction
参数：s₁ s₂ : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.vsub_self_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s
 t : Set β}, s ⊆ t → s -ᵥ s ⊆ t -ᵥ t
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
The sup of the directions of two affine subspaces is less than or equal to the d
irection of
their sup.
-/
theorem sup_direction_le (s₁ s₂ : AffineSubspace k P) :
    s₁.direction ⊔ s₂.direction ≤ (s₁ ⊔ s₂).direction := by
  simp only [direction_eq_vectorSpan, vectorSpan_def]
  exact
    sup_le
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_left : s₁ ≤ s₁ ⊔ s₂)) hp)
      (sInf_le_sInf fun p hp => Set.Subset.trans (vsub_self_mono (le_sup_right : s₂ ≤ s₁ ⊔ s₂)) hp)

/-- The sup of the directions of two nonempty affine subspaces with empty intersection is less than
the direction of their sup. -/
/-
**AffineSubspace.sup_direction_lt_of_nonempty_of_inter_empty** 是 Mathlib 中的一个定理，
位于命名空间 `AffineSubspace`。
形式化陈述：sup_direction_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P} (
h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁ inter s₂ : Se
t P) = ∅) : s₁.direction ⊔ s₂.direction < (s₁ ⊔ s₂).direction
参数：h1 : (s₁ : Set P).Nonempty；h2 : (s₂ : Set P).Nonempty；he : (s₁ inter s₂ : Set
 P) = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `AffineSubspace.sup_direction_le`：sup_direction_le (s₁ s₂ : AffineSubspac
e k P) : s₁.direction ⊔ s₂.direction <= (s₁ ⊔ s₂).direction
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …

--- 原说明 ---
The sup of the directions of two nonempty affine subspaces with empty intersecti
on is less than
the direction of their sup.
-/
theorem sup_direction_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁ ∩ s₂ : Set P) = ∅) :
    s₁.direction ⊔ s₂.direction < (s₁ ⊔ s₂).direction := by
  obtain ⟨p₁, hp₁⟩ := h1
  obtain ⟨p₂, hp₂⟩ := h2
  rw [SetLike.lt_iff_le_and_exists]
  use sup_direction_le s₁ s₂, p₂ -ᵥ p₁,
    vsub_mem_direction ((le_sup_right : s₂ ≤ s₁ ⊔ s₂) hp₂) ((le_sup_left : s₁ ≤ s₁ ⊔ s₂) hp₁)
  intro h
  rw [Submodule.mem_sup] at h
  rcases h with ⟨v₁, hv₁, v₂, hv₂, hv₁v₂⟩
  rw [← sub_eq_zero, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm v₁, add_assoc, ←
    vadd_vsub_assoc, ← neg_neg v₂, add_comm, ← sub_eq_add_neg, ← vsub_vadd_eq_vsub_sub,
    vsub_eq_zero_iff_eq] at hv₁v₂
  refine Set.Nonempty.ne_empty ?_ he
  use v₁ +ᵥ p₁, vadd_mem_of_mem_direction hv₁ hp₁
  rw [hv₁v₂]
  exact vadd_mem_of_mem_direction (Submodule.neg_mem _ hv₂) hp₂

/-- If the directions of two nonempty affine subspaces span the whole module, they have nonempty
intersection. -/
/-
**AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top** 是 Mathlib 
中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：inter_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace
 k P} (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (hd : s₁.directi
on ⊔ s₂.direction = ⊤) : ((s₁ : Set P) inter s₂).Nonempty
参数：h1 : (s₁ : Set P).Nonempty；h2 : (s₂ : Set P).Nonempty；hd : s₁.direction ⊔ s₂.
direction = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `AffineSubspace.sup_direction_lt_of_nonempty_of_inter_empty`：sup_directio
n_lt_of_nonempty_of_inter_empty {s₁ s₂ : AffineSubspace k P} (h1 : (s₁ : Set P).
Nonempty) (h2 : (s₂ : Set P).Nonempty) (he : (s₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a

--- 原说明 ---
If the directions of two nonempty affine subspaces span the whole module, they h
ave nonempty
intersection.
-/
theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : s₁.direction ⊔ s₂.direction = ⊤) : ((s₁ : Set P) ∩ s₂).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hlt := sup_direction_lt_of_nonempty_of_inter_empty h1 h2 h
  rw [hd] at hlt
  exact not_top_lt hlt

/-- If the directions of two nonempty affine subspaces are complements of each other, they intersect
in exactly one point. -/
/-
**AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl** 是 Mathlib 中的一个定理，位于
命名空间 `AffineSubspace`。
形式化陈述：inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P} (h1
 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (hd : IsCompl s₁.directio
n s₂.direction) : exists p, (s₁ : Set P) inter s₂ = {p}
参数：h1 : (s₁ : Set P).Nonempty；h2 : (s₂ : Set P).Nonempty；hd : IsCompl s₁.directi
on s₂.direction。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top`：inter
_nonempty_of_nonempty_of_sup_direction_eq_top {s₁ s₂ : AffineSubspace k P} (h1 :
 (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty) (h…
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the directions of two nonempty affine subspaces are complements of each other
, they intersect
in exactly one point.
-/
theorem inter_eq_singleton_of_nonempty_of_isCompl {s₁ s₂ : AffineSubspace k P}
    (h1 : (s₁ : Set P).Nonempty) (h2 : (s₂ : Set P).Nonempty)
    (hd : IsCompl s₁.direction s₂.direction) : ∃ p, (s₁ : Set P) ∩ s₂ = {p} := by
  obtain ⟨p, hp⟩ := inter_nonempty_of_nonempty_of_sup_direction_eq_top h1 h2 hd.sup_eq_top
  use p
  ext q
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq1, hq2⟩
    have hqp : q -ᵥ p ∈ s₁.direction ⊓ s₂.direction :=
      ⟨vsub_mem_direction hq1 hp.1, vsub_mem_direction hq2 hp.2⟩
    rwa [hd.inf_eq_bot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hqp
  · exact fun h => h.symm ▸ hp

/-- Coercing a subspace to a set then taking the affine span produces the original subspace. -/
@[simp]
/-
**AffineSubspace.affineSpan_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：affineSpan_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s
参数：s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s

--- 原说明 ---
Coercing a subspace to a set then taking the affine span produces the original s
ubspace.
-/
theorem affineSpan_coe (s : AffineSubspace k P) : affineSpan k (s : Set P) = s := by
  refine le_antisymm ?_ (subset_affineSpan _ _)
  rintro p ⟨p₁, hp₁, v, hv, rfl⟩
  exact vadd_mem_of_mem_direction hv hp₁

@[simp, gcongr]
/-
**AffineSubspace.mk'_le_mk'_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V P] (p : P) {d₁ d₂
 : Submodule k V}, AffineSubspace.mk' p d₁ ≤ AffineSubspace.mk' p d₂ ↔ d₁ ≤ d₂
参数：p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
-/
theorem mk'_le_mk'_iff (p : P) {d₁ d₂ : Submodule k V} : mk' p d₁ ≤ mk' p d₂ ↔ d₁ ≤ d₂ := by
  simp_rw [SetLike.le_def, mem_mk']
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h hx⟩
  simpa using h (show (x +ᵥ p) -ᵥ p ∈ d₁ by simpa using hx)
/-
**AffineSubspace.mk'_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V P] (p : P), Stric
tMono (AffineSubspace.mk' p)
参数：p : P；AffineSubspace.mk' p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AffineSubspace.mk'_le_mk'_iff`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
S : AddTorsor V P] …
-/
theorem mk'_strictMono (p : P) : StrictMono (mk' p (k := k)) :=
  strictMono_of_le_iff_le (fun _ _ ↦ (mk'_le_mk'_iff p).symm)

end AffineSubspace

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {ι : Type*}

open AffineSubspace

section

variable {s : Set P}

/-- The affine span of a set is nonempty if and only if that set is. -/
/-
**affineSpan_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_nonempty : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spanPoints_nonempty`：spanPoints_nonempty (s : Set P) : (spanPoints k s).
Nonempty ↔ s.Nonempty

--- 原说明 ---
The affine span of a set is nonempty if and only if that set is.
-/
theorem affineSpan_nonempty : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty :=
  spanPoints_nonempty k s

alias ⟨_, _root_.Set.Nonempty.affineSpan⟩ := affineSpan_nonempty

/-- The affine span of a nonempty set is nonempty. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine span of a nonempty set is nonempty.
-/
instance [Nonempty s] : Nonempty (affineSpan k s) :=
  ((nonempty_coe_sort.1 ‹_›).affineSpan _).to_subtype

/-- The affine span of a set is `⊥` if and only if that set is empty. -/
@[simp]
/-
**affineSpan_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `AffineSubspace.nonempty_iff_ne_bot`：nonempty_iff_ne_bot (Q : AffineSubsp
ace k P) : (Q : Set P).Nonempty ↔ Q != ⊥
· 使用定理 `affineSpan_nonempty`：affineSpan_nonempty : (affineSpan k s : Set P).None
mpty ↔ s.Nonempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The affine span of a set is `⊥` if and only if that set is empty.
-/
theorem affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅ := by
  rw [← not_iff_not, ← Ne, ← Ne, ← nonempty_iff_ne_bot, affineSpan_nonempty,
    nonempty_iff_ne_empty]

@[simp]
/-
**bot_lt_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_lt_affineSpan : ⊥ < affineSpan k s ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `affineSpan_eq_bot`：affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅
-/
theorem bot_lt_affineSpan : ⊥ < affineSpan k s ↔ s.Nonempty := by
  rw [bot_lt_iff_ne_bot, nonempty_iff_ne_empty]
  exact (affineSpan_eq_bot _).not

@[simp]
/-
**affineSpan_eq_top_iff_nonempty_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_eq_top_iff_nonempty_of_subsingleton [Subsingleton P] : affineSp
an k s = ⊤ ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_lt_affineSpan`：bot_lt_affineSpan : ⊥ < affineSpan k s ↔ s.Nonempty
· 使用定理 `IsSimpleOrder.bot_lt_iff_eq_top`：∀ {α : Type u_2} [inst : PartialOrder α
] [inst_1 : BoundedOrder α] [IsSimpleOrder α] {a : α}, ⊥ < a ↔ a = ⊤
· 使用定理 `AffineSubspace.instIsSimpleOrderOfSubsingleton`：∀ {k : Type u_1} {V : Ty
pe u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root
_.Module k V]   [S : AddTorsor V P] …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma affineSpan_eq_top_iff_nonempty_of_subsingleton [Subsingleton P] :
    affineSpan k s = ⊤ ↔ s.Nonempty := by
  rw [← bot_lt_affineSpan k, IsSimpleOrder.bot_lt_iff_eq_top]

end

variable {k}

/-- An induction principle for span membership. If `p` holds for all elements of `s` and is
preserved under certain affine combinations, then `p` holds for all elements of the span of `s`. -/
@[elab_as_elim]
/-
**affineSpan_induction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_induction {x : P} {s : Set P} {p : P -> Prop} (h : x in affineS
pan k s) (mem : forall x : P, x in s -> p x) (smul_vsub_vadd : forall (c : k) (u
 v w : P), p u -> p v -> p w -> p (c • (u -ᵥ v) +ᵥ w)) : p x
参数：h : x in affineSpan k s；mem : forall x : P, x in s -> p x；smul_vsub_vadd : fo
rall (c : k) (u v w : P), p u -> p v -> p w -> p (c • (u -ᵥ v) +ᵥ w)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …

--- 原说明 ---
An induction principle for span membership. If `p` holds for all elements of `s`
 and is
preserved under certain affine combinations, then `p` holds for all elements of 
the span of `s`.
-/
theorem affineSpan_induction {x : P} {s : Set P} {p : P → Prop} (h : x ∈ affineSpan k s)
    (mem : ∀ x : P, x ∈ s → p x)
    (smul_vsub_vadd : ∀ (c : k) (u v w : P), p u → p v → p w → p (c • (u -ᵥ v) +ᵥ w)) : p x :=
  (affineSpan_le (Q := ⟨{x | p x}, smul_vsub_vadd⟩)).mpr mem h

/-- A dependent version of `affineSpan_induction`. -/
@[elab_as_elim]
/-
**affineSpan_induction'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_induction' {s : Set P} {p : forall x, x in affineSpan k s -> Pr
op} (mem : forall (y) (hys : y in s), p y (subset_affineSpan k _ hys)) (smul_vsu
b_vadd : forall (c : k) (u hu v hv w hw), p u hu -> p v hv -> p w hw -> p (c • (
u -ᵥ v) +ᵥ w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw)) {x : P} (h : x i
n affineSpan k s) : p x h
参数：mem : forall (y) (hys : y in s), p y (subset_affineSpan k _ hys)；smul_vsub_va
dd : forall (c : k) (u hu v hv w hw), p u hu -> p v hv -> p w hw -> p (c • (u -ᵥ
 v) +ᵥ w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw)；h : x in affineSpan k
 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用引理 `AffineSubspace.smul_vsub_vadd_mem`：smul_vsub_vadd_mem (s : AffineSubspac
e k P) (c : k) {p₁ p₂ p₃ : P} : p₁ in s -> p₂ in s -> p₃ in s -> c • (p₁ -ᵥ p₂ :
 V) +ᵥ p₃ in s
· 使用定理 `affineSpan_induction`：affineSpan_induction {x : P} {s : Set P} {p : P ->
 Prop} (h : x in affineSpan k s) (mem : forall x : P, x in s -> p x) (smul_vsub_
vadd : for…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b

--- 原说明 ---
A dependent version of `affineSpan_induction`.
-/
theorem affineSpan_induction' {s : Set P} {p : ∀ x, x ∈ affineSpan k s → Prop}
    (mem : ∀ (y) (hys : y ∈ s), p y (subset_affineSpan k _ hys))
    (smul_vsub_vadd : ∀ (c : k) (u hu v hv w hw), p u hu → p v hv → p w hw →
      p (c • (u -ᵥ v) +ᵥ w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw))
    {x : P} (h : x ∈ affineSpan k s) : p x h := by
  suffices ∃ (hx : x ∈ affineSpan k s), p x hx from this.elim fun hx hc ↦ hc
  -- TODO: `induction h using affineSpan_induction` gives the error:
  -- extra targets for '@affineSpan_induction'
  -- It seems that the `induction` tactic has decided to ignore the clause
  -- `using affineSpan_induction` and use `Exists.rec` instead.
  refine affineSpan_induction h ?mem ?smul_vsub_vadd
  · exact fun y hy ↦ ⟨subset_affineSpan _ _ hy, mem y hy⟩
  · exact fun c u v w hu hv hw ↦
      hu.elim fun hu' hu ↦ hv.elim fun hv' hv ↦ hw.elim fun hw' hw ↦
        ⟨AffineSubspace.smul_vsub_vadd_mem _ _ hu' hv' hw',
              smul_vsub_vadd _ _ _ _ _ _ _ hu hv hw⟩

variable (k)

/-- The difference between two points lies in their `vectorSpan`. -/
/-
**vsub_mem_vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vsub_mem_vectorSpan_pair (p₁ p₂ : P) : p₁ -ᵥ p₂ in vectorSpan k ({p₁, p₂} 
: Set P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
The difference between two points lies in their `vectorSpan`.
-/
theorem vsub_mem_vectorSpan_pair (p₁ p₂ : P) : p₁ -ᵥ p₂ ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  vsub_mem_vectorSpan _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The difference between two points (reversed) lies in their `vectorSpan`. -/
/-
**vsub_rev_mem_vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vsub_rev_mem_vectorSpan_pair (p₁ p₂ : P) : p₂ -ᵥ p₁ in vectorSpan k ({p₁, 
p₂} : Set P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
The difference between two points (reversed) lies in their `vectorSpan`.
-/
theorem vsub_rev_mem_vectorSpan_pair (p₁ p₂ : P) : p₂ -ᵥ p₁ ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  vsub_mem_vectorSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (Set.mem_insert _ _)

variable {k}

/-- A multiple of the difference between two points lies in their `vectorSpan`. -/
/-
**smul_vsub_mem_vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_vsub_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) : r • (p₁ -ᵥ p₂) in vect
orSpan k ({p₁, p₂} : Set P)
参数：r : k；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `vsub_mem_vectorSpan_pair`：vsub_mem_vectorSpan_pair (p₁ p₂ : P) : p₁ -ᵥ p
₂ in vectorSpan k ({p₁, p₂} : Set P)

--- 原说明 ---
A multiple of the difference between two points lies in their `vectorSpan`.
-/
theorem smul_vsub_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₁ -ᵥ p₂) ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  Submodule.smul_mem _ _ (vsub_mem_vectorSpan_pair k p₁ p₂)

/-- A multiple of the difference between two points (reversed) lies in their `vectorSpan`. -/
/-
**smul_vsub_rev_mem_vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_vsub_rev_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) in 
vectorSpan k ({p₁, p₂} : Set P)
参数：r : k；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `vsub_rev_mem_vectorSpan_pair`：vsub_rev_mem_vectorSpan_pair (p₁ p₂ : P) :
 p₂ -ᵥ p₁ in vectorSpan k ({p₁, p₂} : Set P)

--- 原说明 ---
A multiple of the difference between two points (reversed) lies in their `vector
Span`.
-/
theorem smul_vsub_rev_mem_vectorSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) ∈ vectorSpan k ({p₁, p₂} : Set P) :=
  Submodule.smul_mem _ _ (vsub_rev_mem_vectorSpan_pair k p₁ p₂)

variable (k)

/-- The line between two points, as an affine subspace. -/
notation3 "line[" k ", " p₁ ", " p₂ "]" =>
  affineSpan k (insert p₁ (@singleton _ _ Set.instSingletonSet p₂))

/-- The first of two points lies in their affine span. -/
/-
**left_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in line[k, p₁, p₂]
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
The first of two points lies in their affine span.
-/
theorem left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ ∈ line[k, p₁, p₂] :=
  mem_affineSpan _ (Set.mem_insert _ _)

/-- The second of two points lies in their affine span. -/
/-
**right_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in line[k, p₁, p₂]
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
The second of two points lies in their affine span.
-/
theorem right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ ∈ line[k, p₁, p₂] :=
  mem_affineSpan _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable {k}

/-- The span of two points that lie in an affine subspace is contained in that subspace. -/
/-
**affineSpan_pair_le_of_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_pair_le_of_mem_of_mem {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁
 : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂] <= s
参数：hp₁ : p₁ in s；hp₂ : p₂ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s

--- 原说明 ---
The span of two points that lie in an affine subspace is contained in that subsp
ace.
-/
theorem affineSpan_pair_le_of_mem_of_mem {p₁ p₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : line[k, p₁, p₂] ≤ s := by
  rw [affineSpan_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp₁, hp₂⟩

/-- One line is contained in another differing in the first point if the first point of the first
line is contained in the second line. -/
/-
**affineSpan_pair_le_of_left_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_pair_le_of_left_mem {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) 
: line[k, p₁, p₃] <= line[k, p₂, p₃]
参数：h : p₁ in line[k, p₂, p₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_pair_le_of_mem_of_mem`：affineSpan_pair_le_of_mem_of_mem {p₁ p
₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂
] <= s
· 使用定理 `right_mem_affineSpan_pair`：right_mem_affineSpan_pair (p₁ p₂ : P) : p₂ in
 line[k, p₁, p₂]

--- 原说明 ---
One line is contained in another differing in the first point if the first point
 of the first
line is contained in the second line.
-/
theorem affineSpan_pair_le_of_left_mem {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    line[k, p₁, p₃] ≤ line[k, p₂, p₃] :=
  affineSpan_pair_le_of_mem_of_mem h (right_mem_affineSpan_pair _ _ _)

/-- One line is contained in another differing in the second point if the second point of the
first line is contained in the second line. -/
/-
**affineSpan_pair_le_of_right_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_pair_le_of_right_mem {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃])
 : line[k, p₂, p₁] <= line[k, p₂, p₃]
参数：h : p₁ in line[k, p₂, p₃]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_pair_le_of_mem_of_mem`：affineSpan_pair_le_of_mem_of_mem {p₁ p
₂ : P} {s : AffineSubspace k P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : line[k, p₁, p₂
] <= s
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]

--- 原说明 ---
One line is contained in another differing in the second point if the second poi
nt of the
first line is contained in the second line.
-/
theorem affineSpan_pair_le_of_right_mem {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    line[k, p₂, p₁] ≤ line[k, p₂, p₃] :=
  affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) h

variable (k)

/-- `affineSpan` is monotone. -/
@[gcongr, mono]
/-
**affineSpan_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : affineSpan k s₁ <= 
affineSpan k s₂
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_le_of_subset_coe`：affineSpan_le_of_subset_coe {s : Set P} {s₁
 : AffineSubspace k P} (h : s subseteq s₁) : affineSpan k s <= s₁
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s

--- 原说明 ---
`affineSpan` is monotone.
-/
theorem affineSpan_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : affineSpan k s₁ ≤ affineSpan k s₂ :=
  affineSpan_le_of_subset_coe (Set.Subset.trans h (subset_affineSpan k _))

/-- Taking the affine span of a set, adding a point and taking the span again produces the same
results as adding the point to the set and taking the span. -/
/-
**affineSpan_insert_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_insert_affineSpan (p : P) (ps : Set P) : affineSpan k (insert p
 (affineSpan k ps : Set P)) = affineSpan k (insert p ps)
参数：p : P；ps : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `AffineSubspace.span_union`：span_union (s t : Set P) : affineSpan k (s un
ion t) = affineSpan k s ⊔ affineSpan k t
· 使用定理 `AffineSubspace.affineSpan_coe`：affineSpan_coe (s : AffineSubspace k P) :
 affineSpan k (s : Set P) = s

--- 原说明 ---
Taking the affine span of a set, adding a point and taking the span again produc
es the same
results as adding the point to the set and taking the span.
-/
theorem affineSpan_insert_affineSpan (p : P) (ps : Set P) :
    affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (insert p ps) := by
  rw [Set.insert_eq, Set.insert_eq, span_union, span_union, affineSpan_coe]

/-- If a point is in the affine span of a set, adding it to that set does not change the affine
span. -/
/-
**affineSpan_insert_eq_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_insert_eq_affineSpan {p : P} {ps : Set P} (h : p in affineSpan 
k ps) : affineSpan k (insert p ps) = affineSpan k ps
参数：h : p in affineSpan k ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `AffineSubspace.mem_coe`：mem_coe (p : P) (s : AffineSubspace k P) : p in 
(s : Set P) ↔ p in s
· 使用定理 `AffineSubspace.affineSpan_coe`：affineSpan_coe (s : AffineSubspace k P) :
 affineSpan k (s : Set P) = s

--- 原说明 ---
If a point is in the affine span of a set, adding it to that set does not change
 the affine
span.
-/
theorem affineSpan_insert_eq_affineSpan {p : P} {ps : Set P} (h : p ∈ affineSpan k ps) :
    affineSpan k (insert p ps) = affineSpan k ps := by
  rw [← mem_coe] at h
  rw [← affineSpan_insert_affineSpan, Set.insert_eq_of_mem h, affineSpan_coe]

variable {k}

/-- If a point is in the affine span of a set, adding it to that set does not change the vector
span. -/
/-
**vectorSpan_insert_eq_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vectorSpan_insert_eq_vectorSpan {p : P} {ps : Set P} (h : p in affineSpan 
k ps) : vectorSpan k (insert p ps) = vectorSpan k ps
参数：h : p in affineSpan k ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `affineSpan_insert_eq_affineSpan`：affineSpan_insert_eq_affineSpan {p : P}
 {ps : Set P} (h : p in affineSpan k ps) : affineSpan k (insert p ps) = affineSp
an k ps
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a point is in the affine span of a set, adding it to that set does not change
 the vector
span.
-/
theorem vectorSpan_insert_eq_vectorSpan {p : P} {ps : Set P} (h : p ∈ affineSpan k ps) :
    vectorSpan k (insert p ps) = vectorSpan k ps := by
  simp_rw [← direction_affineSpan, affineSpan_insert_eq_affineSpan _ h]

/-- When the affine space is also a vector space, the affine span is contained within the linear
span. -/
/-
**affineSpan_le_toAffineSubspace_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_le_toAffineSubspace_span {s : Set V} : affineSpan k s <= (Submo
dule.span k s).toAffineSubspace
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_induction'`：affineSpan_induction' {s : Set P} {p : forall x, 
x in affineSpan k s -> Prop} (mem : forall (y) (hys : y in s), p y (subset_affin
eSpan k _ h…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …

--- 原说明 ---
When the affine space is also a vector space, the affine span is contained withi
n the linear
span.
-/
lemma affineSpan_le_toAffineSubspace_span {s : Set V} :
    affineSpan k s ≤ (Submodule.span k s).toAffineSubspace := by
  intro x hx
  simp only [Submodule.mem_toAffineSubspace]
  induction hx using affineSpan_induction' with
  | mem x hx => exact Submodule.subset_span hx
  | smul_vsub_vadd c u _ v _ w _ hu hv hw =>
    simp only [vsub_eq_sub, vadd_eq_add]
    apply Submodule.add_mem _ _ hw
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu hv)
/-
**affineSpan_subset_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_subset_span {s : Set V} : (affineSpan k s : Set V) subseteq Sub
module.span k s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `affineSpan_le_toAffineSubspace_span`：affineSpan_le_toAffineSubspace_span
 {s : Set V} : affineSpan k s <= (Submodule.span k s).toAffineSubspace
-/
lemma affineSpan_subset_span {s : Set V} :
    (affineSpan k s : Set V) ⊆ Submodule.span k s :=
  affineSpan_le_toAffineSubspace_span

-- TODO: We want this to be simp, but `affineSpan` gets simp-ed away to `spanPoints`!
-- Let's delete `spanPoints`
/-
**affineSpan_insert_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：affineSpan_insert_zero (s : Set V) : (affineSpan k (insert 0 s) : Set V) =
 Submodule.span k s
参数：s : Set V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_insert_zero`：span_insert_zero : span R (insert (0 : M) s)
 = span R s
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `affineSpan_subset_span`：affineSpan_subset_span {s : Set V} : (affineSpan
 k s : Set V) subseteq Submodule.span k s
· 使用引理 `vectorSpan_add_self`：vectorSpan_add_self (s : Set V) : (vectorSpan k s :
 Set V) + s = affineSpan k s
· 使用定理 `vectorSpan_def`：vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.
span k (s -ᵥ s)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.subset_sub_left`：∀ {α : Type u_2} [inst : SubtractionMonoid α] {s t 
: Set α}, 0 ∈ t → s ⊆ s - t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.subset_add_left`：∀ {α : Type u_2} [inst : AddZeroClass α] (s : Set α
) {t : Set α}, 0 ∈ t → s ⊆ s + t
-/
lemma affineSpan_insert_zero (s : Set V) :
    (affineSpan k (insert 0 s) : Set V) = Submodule.span k s := by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self, vectorSpan_def]
  refine Subset.trans ?_ <| subset_add_left _ <| mem_insert ..
  gcongr
  exact subset_sub_left <| mem_insert ..

end AffineSpace'

