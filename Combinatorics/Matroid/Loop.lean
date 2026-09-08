/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Tactic.TFAE

/-!
# Matroid loops and coloops

## Loops
A 'loop' of a matroid `M` is an element `e` satisfying one of the following equivalent conditions:
* `e ∈ M.closure ∅`;
* `{e}` is dependent in `M`;
* `{e}` is a circuit of `M`;
* no base of `M` contains `e`.

In many mathematical contexts, loops can be thought of as 'trivial' or 'zero' elements;
For linearly representable matroids, they correspond to the zero vector,
and for graphic matroids, they correspond to edges incident with just one vertex (aka 'loops').
As trivial as they are, loops can be created from matroids with no loops by taking minors or duals,
so in many contexts it is unreasonable to simply forbid loops from appearing.
For `M : Matroid α`, this file defines a set `Matroid.loops M : Set α`,
as well as predicates `Matroid.IsLoop M : α → Prop` and `Matroid.IsNonloop M : α → Prop`,
and provides API for interacting with them.

## Coloops
The dual notion of a loop is a 'coloop'. Geometrically, these can be thought of elements that are
skew to the remainder of the matroid. Coloops in graphic matroids are 'bridge' edges of the graph,
and coloops in linearly representable matroids are vectors not spanned by the other vectors
in the matroid.
Coloops also have many equivalent definitions in abstract matroid language;
a coloop is an element of `M.E` if any of the following equivalent conditions holds :
* `e` is a loop of `M✶`;
* `{e}` is a cocircuit of `M`;
* `e` is in no circuit of `M`;
* `e` is in every base of `M`;
* for all `X ⊆ M.E`, `e ∈ X ↔ e ∈ M.closure X`,
* `M.E \ {e}` is nonspanning.

## Main Declarations
For `M` : Matroid `α`:
* `M.loops` is the set `M.closure ∅`.
* `M.IsLoop e` means that `e : α` is a loop of `M`, defined as the statement `e ∈ M.loops`.
* `M.isLoop_tfae` gives a number of properties that are equivalent to `IsLoop`.
* `M.IsNonloop e` means that `e ∈ M.E`, but `e` is not a loop of `M`.
* `M.IsColoop e ` means that `e` is a loop of `M✶`.
* `M.coloops` is the set of coloops of `M✶`.
* `M.isColoop_tfae` gives a number of properties that are equivalent to `IsColoop`.
* `M.Loopless` is a typeclass meaning `M` has no loops.
* `M.removeLoops` is the matroid obtained from `M` by restricting to its set of nonloop elements.
-/

@[expose] public section

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set

namespace Matroid

/-- `Matroid.loops M` is the closure of the empty set. -/
/-
**Matroid.loops** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：loops (M : Matroid α)
参数：M : Matroid α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matroid.loops M` is the closure of the empty set.
-/
def loops (M : Matroid α) := M.closure ∅

@[aesop unsafe 20% (rule_sets := [Matroid])]
/-
**Matroid.loops_subset_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：loops_subset_ground (M : Matroid α) : M.loops subseteq M.E
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
-/
lemma loops_subset_ground (M : Matroid α) : M.loops ⊆ M.E :=
  M.closure_subset_ground ∅

/-- A 'loop' is a member of the closure of the empty set -/
/-
**Matroid.IsLoop** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsLoop (M : Matroid α) (e : α) : Prop
参数：M : Matroid α；e : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 'loop' is a member of the closure of the empty set
-/
def IsLoop (M : Matroid α) (e : α) : Prop := e ∈ M.loops
/-
**Matroid.isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isLoop_iff : M.IsLoop e ↔ e in M.loops
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLoop_iff : M.IsLoop e ↔ e ∈ M.loops := Iff.rfl
/-
**Matroid.closure_empty** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_empty (M : Matroid α) : M.closure ∅ = M.loops
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma closure_empty (M : Matroid α) : M.closure ∅ = M.loops := rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
/-
**Matroid.IsLoop.mem_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → e ∈ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
-/
lemma IsLoop.mem_ground (he : M.IsLoop e) : e ∈ M.E :=
  closure_subset_ground M ∅ he
/-
**Matroid.isLoop_tfae** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [ M.IsLoop e, e in M.closu
re ∅, M.IsCircuit {e}, M.Dep {e}, forall ⦃B⦄, M.IsBase B -> e in M.E \ B]
参数：M : Matroid α；e : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.mem_closure_iff_of_notMem`：∀ {α : Type u_2} {M : Matroid α
} {e : α} {I : Set α}, M.Indep I → e ∉ I → (e ∈ M.closure I ↔ M.Dep (insert e I)
)
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [
    M.IsLoop e,
    e ∈ M.closure ∅,
    M.IsCircuit {e},
    M.Dep {e},
    ∀ ⦃B⦄, M.IsBase B → e ∈ M.E \ B] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e),
    isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]
  tfae_have 2 ↔ 4 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e)]
  tfae_have 4 ↔ 5 := by
    simp only [dep_iff, singleton_subset_iff, mem_sdiff, forall_and]
    refine ⟨fun h ↦ ⟨fun _ _ ↦ h.2, fun B hB heB ↦ h.1 (hB.indep.subset (by simpa))⟩,
      fun h ↦ ⟨fun hi ↦ ?_, h.1 _ M.exists_isBase.choose_spec⟩⟩
    obtain ⟨B, hB, heB⟩ := hi.exists_isBase_superset
    exact h.2 _ hB (by simpa using heB)
  tfae_finish

@[simp]
/-
**Matroid.singleton_dep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：singleton_dep : M.Dep {e} ↔ M.IsLoop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isLoop_tfae`：isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [ M
.IsLoop e, e in M.closure ∅, M.IsCircuit {e}, M.Dep {e}, forall ⦃B⦄, M.IsBase B 
-> e in M…
-/
lemma singleton_dep : M.Dep {e} ↔ M.IsLoop e :=
  (M.isLoop_tfae e).out 3 0

alias ⟨_, IsLoop.dep⟩ := singleton_dep
/-
**Matroid.singleton_not_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：singleton_not_indep (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.singleton_dep`：singleton_dep : M.Dep {e} ↔ M.IsLoop e
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬ M.Indep {e} ↔ M.IsLoop e := by
  rw [← singleton_dep, ← not_indep_iff]

@[simp]
/-
**Matroid.singleton_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：singleton_isCircuit : M.IsCircuit {e} ↔ M.IsLoop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isLoop_tfae`：isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [ M
.IsLoop e, e in M.closure ∅, M.IsCircuit {e}, M.Dep {e}, forall ⦃B⦄, M.IsBase B 
-> e in M…
-/
lemma singleton_isCircuit : M.IsCircuit {e} ↔ M.IsLoop e :=
  (M.isLoop_tfae e).out 2 0

alias ⟨_, IsLoop.isCircuit⟩ := singleton_isCircuit
/-
**Matroid.isLoop_iff_forall_mem_compl_isBase** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：isLoop_iff_forall_mem_compl_isBase : M.IsLoop e ↔ forall B, M.IsBase B -> 
e in M.E \ B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isLoop_tfae`：isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [ M
.IsLoop e, e in M.closure ∅, M.IsCircuit {e}, M.Dep {e}, forall ⦃B⦄, M.IsBase B 
-> e in M…
-/
lemma isLoop_iff_forall_mem_compl_isBase : M.IsLoop e ↔ ∀ B, M.IsBase B → e ∈ M.E \ B :=
  (M.isLoop_tfae e).out 0 4
/-
**Matroid.isLoop_iff_forall_notMem_isBase** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isLoop_iff_forall_notMem_isBase (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLoop_iff_forall_notMem_isBase (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ ∀ B, M.IsBase B → e ∉ B := by
  simp_rw [isLoop_iff_forall_mem_compl_isBase, mem_sdiff, and_iff_right he]
/-
**Matroid.IsLoop.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → ∀ (X : Set α), e ∈ 
M.closure X
参数：X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_mono`：closure_mono (M : Matroid α) : Monotone M.closure
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
lemma IsLoop.mem_closure (he : M.IsLoop e) (X : Set α) : e ∈ M.closure X :=
  M.closure_mono (empty_subset _) he
/-
**Matroid.IsLoop.mem_of_isFlat** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → ∀ {F : Set α}, M.Is
Flat F → e ∈ F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.mem_closure`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.
IsLoop e → ∀ (X : Set α), e ∈ M.closure X
· 使用定理 `Matroid.IsFlat.closure`：∀ {α : Type u_2} {M : Matroid α} {F : Set α}, M.
IsFlat F → M.closure F = F
-/
lemma IsLoop.mem_of_isFlat (he : M.IsLoop e) {F : Set α} (hF : M.IsFlat F) : e ∈ F :=
  hF.closure ▸ he.mem_closure F
/-
**Matroid.IsFlat.loops_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsFlat`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {F : Set α}, M.IsFlat F → M.loops ⊆ F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.mem_of_isFlat`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsLoop e → ∀ {F : Set α}, M.IsFlat F → e ∈ F
-/
lemma IsFlat.loops_subset (hF : M.IsFlat F) : M.loops ⊆ F :=
  fun _ he ↦ IsLoop.mem_of_isFlat he hF
/-
**Matroid.IsLoop.dep_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {X : Set α},   M.IsLoop e → e ∈ X
 → autoParam (X ⊆ M.E) Matroid.IsLoop.dep_of_mem._auto_1 → M.Dep X
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.superset`：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   
M.Dep D → D ⊆ X → autoParam (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
· 使用定理 `Matroid.IsLoop.dep`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e
 → M.Dep {e}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma IsLoop.dep_of_mem (he : M.IsLoop e) (h : e ∈ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE
/-
**Matroid.IsLoop.not_indep_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {X : Set α}, M.IsLoop e → e ∈ X →
 ¬M.Indep X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsLoop.dep`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e
 → M.Dep {e}
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma IsLoop.not_indep_of_mem (he : M.IsLoop e) (h : e ∈ X) : ¬M.Indep X :=
  fun hX ↦ he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))
/-
**Matroid.IsLoop.notMem_of_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {I : Set α}, M.IsLoop e → M.Indep
 I → e ∉ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.not_indep_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α
} {X : Set α}, M.IsLoop e → e ∈ X → ¬M.Indep X
-/
lemma IsLoop.notMem_of_indep (he : M.IsLoop e) (hI : M.Indep I) : e ∉ I :=
  fun h ↦ he.not_indep_of_mem h hI
/-
**Matroid.IsLoop.eq_of_isCircuit_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α}, M.IsLoop e → M.IsCir
cuit C → e ∈ C → C = {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsCircuit.eq_of_subset_isCircuit`：∀ {α : Type u_1} {M : Matroid 
α} {C C' : Set α}, M.IsCircuit C → M.IsCircuit C' → C ⊆ C' → C = C'
· 使用定理 `Matroid.IsLoop.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.Is
Loop e → M.IsCircuit {e}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma IsLoop.eq_of_isCircuit_mem (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e ∈ C) : C = {e} := by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]
/-
**Matroid.Indep.disjoint_loops** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → Disjoint I M.loo
ps
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Matroid.IsLoop.notMem_of_indep`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.IsLoop e → M.Indep I → e ∉ I
-/
lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I M.loops :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.notMem_of_indep he hI heI
/-
**Matroid.Indep.eq_empty_of_subset_loops** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Inde
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → I ⊆ M.loops → I 
= ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Matroid.IsLoop.notMem_of_indep`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.IsLoop e → M.Indep I → e ∉ I
-/
lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.loops) : I = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ he ↦ IsLoop.notMem_of_indep (h he) hI he

@[simp]
/-
**Matroid.isBasis_loops_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isBasis_loops_iff : M.IsBasis I M.loops ↔ I = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.eq_empty_of_subset_loops`：∀ {α : Type u_1} {M : Matroid α}
 {I : Set α}, M.Indep I → I ⊆ M.loops → I = ∅
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isBasis_loops_iff : M.IsBasis I M.loops ↔ I = ∅ :=
  ⟨fun h ↦ h.indep.eq_empty_of_subset_loops h.subset,
    by simp +contextual [closure_empty]⟩
/-
**Matroid.closure_eq_loops_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_eq_loops_of_subset (h : X subseteq M.loops) : M.closure X = M.loop
s
参数：h : X subseteq M.loops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用引理 `Matroid.closure_mono`：closure_mono (M : Matroid α) : Monotone M.closure
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
lemma closure_eq_loops_of_subset (h : X ⊆ M.loops) : M.closure X = M.loops :=
  (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))
/-
**Matroid.isBasis_iff_empty_of_subset_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isBasis_iff_empty_of_subset_loops (hX : X subseteq M.loops) : M.IsBasis I 
X ↔ I = ∅
参数：hX : X subseteq M.loops。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用引理 `Matroid.closure_eq_loops_of_subset`：closure_eq_loops_of_subset (h : X su
bseteq M.loops) : M.closure X = M.loops
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isBasis_iff_empty_of_subset_loops (hX : X ⊆ M.loops) : M.IsBasis I X ↔ I = ∅ := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simpa⟩
  have := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using this
/-
**Matroid.IsLoop.closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → M.closure {e} = M.l
oops
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_eq_loops_of_subset`：closure_eq_loops_of_subset (h : X su
bseteq M.loops) : M.closure X = M.loops
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
lemma IsLoop.closure (he : M.IsLoop e) : M.closure {e} = M.loops :=
  closure_eq_loops_of_subset (singleton_subset_iff.mpr he)
/-
**Matroid.isLoop_iff_closure_eq_loops_and_mem_ground** 是 Mathlib 中的一个引理，位于命名空间 `
Matroid`。
形式化陈述：isLoop_iff_closure_eq_loops_and_mem_ground : M.IsLoop e ↔ M.closure {e} = 
M.loops ∧ e in M.E where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.closure`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLo
op e → M.closure {e} = M.loops
· 使用定理 `Matroid.IsLoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.I
sLoop e → e ∈ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isLoop_iff`：isLoop_iff : M.IsLoop e ↔ e in M.loops
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_empty`：closure_empty (M : Matroid α) : M.closure ∅ = M.l
oops
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `Matroid.closure_subset_closure_iff_subset_closure`：closure_subset_closur
e_iff_subset_closure (hX : X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.loops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.loops = M.closur
e ∅
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isLoop_iff_closure_eq_loops_and_mem_ground :
    M.IsLoop e ↔ M.closure {e} = M.loops ∧ e ∈ M.E where
  mp h := ⟨h.closure, h.mem_ground⟩
  mpr h := by
    rw [isLoop_iff, ← closure_empty, ← singleton_subset_iff,
      ← closure_subset_closure_iff_subset_closure, h.1, loops]
/-
**Matroid.isLoop_iff_closure_eq_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isLoop_iff_closure_eq_loops (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isLoop_iff_closure_eq_loops_and_mem_ground`：isLoop_iff_closure_e
q_loops_and_mem_ground : M.IsLoop e ↔ M.closure {e} = M.loops ∧ e in M.E where m
p h
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLoop_iff_closure_eq_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ M.closure {e} = M.loops := by
  rw [isLoop_iff_closure_eq_loops_and_mem_ground, and_iff_left he]

@[simp]
/-
**Matroid.closure_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_loops (M : Matroid α) : M.closure M.loops = M.loops
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
-/
lemma closure_loops (M : Matroid α) : M.closure M.loops = M.loops :=
  M.closure_closure ∅

@[simp]
/-
**Matroid.closure_union_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_union_loops_eq (M : Matroid α) (X : Set α) : M.closure (X union M.
loops) = M.closure X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_empty`：closure_empty (M : Matroid α) : M.closure ∅ = M.l
oops
· 使用定理 `Matroid.closure_union_closure_right_eq`：∀ {α : Type u_2} (M : Matroid α)
 (X Y : Set α), M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y)
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
lemma closure_union_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.loops) = M.closure X := by
  rw [← closure_empty, closure_union_closure_right_eq, union_empty]

@[simp]
/-
**Matroid.closure_loops_union_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_loops_union_eq (M : Matroid α) (X : Set α) : M.closure (M.loops un
ion X) = M.closure X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Matroid.closure_union_loops_eq`：closure_union_loops_eq (M : Matroid α) (
X : Set α) : M.closure (X union M.loops) = M.closure X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma closure_loops_union_eq (M : Matroid α) (X : Set α) :
    M.closure (M.loops ∪ X) = M.closure X := by
  simp [union_comm]
/-
**Matroid.closure_sdiff_loops_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) (X : Set α), M.closure (X \ M.loops) = M.
closure X
参数：M : Matroid α；X : Set α；X \ M.loops。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_union_loops_eq`：closure_union_loops_eq (M : Matroid α) (
X : Set α) : M.closure (X union M.loops) = M.closure X
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用引理 `Matroid.closure_empty`：closure_empty (M : Matroid α) : M.closure ∅ = M.l
oops
· 使用定理 `Matroid.closure_union_closure_right_eq`：∀ {α : Type u_2} (M : Matroid α)
 (X Y : Set α), M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y)
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
@[simp] lemma closure_sdiff_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X \ M.loops) = M.closure X := by
  rw [← M.closure_union_loops_eq (X \ M.loops), sdiff_union_self, ← closure_empty,
    closure_union_closure_right_eq, union_empty]

@[deprecated (since := "2026-06-03")] alias closure_diff_loops_eq := closure_sdiff_loops_eq

/-- A version of `restrict_loops_eq` without the hypothesis that `R ⊆ M.E` -/
/-
**Matroid.restrict_loops_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_loops_eq' (M : Matroid α) (R : Set α) : (M ↾ R).loops = (M.loops 
inter R) union (R \ M.E)
参数：M : Matroid α；R : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_empty`：closure_empty (M : Matroid α) : M.closure ∅ = M.l
oops
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅

--- 原说明 ---
A version of `restrict_loops_eq` without the hypothesis that `R ⊆ M.E`
-/
lemma restrict_loops_eq' (M : Matroid α) (R : Set α) :
    (M ↾ R).loops = (M.loops ∩ R) ∪ (R \ M.E) := by
  rw [← closure_empty, ← closure_empty, restrict_closure_eq', empty_inter]
/-
**Matroid.restrict_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_loops_eq {R : Set α} (hR : R subseteq M.E) : (M ↾ R).loops = M.lo
ops inter R
参数：hR : R subseteq M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.restrict_loops_eq'`：restrict_loops_eq' (M : Matroid α) (R : Set 
α) : (M ↾ R).loops = (M.loops inter R) union (R \ M.E)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
lemma restrict_loops_eq {R : Set α} (hR : R ⊆ M.E) : (M ↾ R).loops = M.loops ∩ R := by
  rw [restrict_loops_eq', sdiff_eq_empty.2 hR, union_empty]

@[simp]
/-
**Matroid.restrict_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_isLoop_iff {R : Set α} : (M ↾ R).IsLoop e ↔ e in R ∧ (M.IsLoop e 
∨ e ∉ M.E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma restrict_isLoop_iff {R : Set α} : (M ↾ R).IsLoop e ↔ e ∈ R ∧ (M.IsLoop e ∨ e ∉ M.E) := by
  simp only [isLoop_iff, restrict_closure_eq', empty_inter, mem_union, mem_inter_iff, mem_sdiff,
    ← closure_empty]
  tauto
/-
**Matroid.IsRestriction.isLoop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestrict
ion`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, N.IsRestriction M → (N.IsLoop 
e ↔ e ∈ N.E ∧ M.IsLoop e)
参数：N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsRestriction.isLoop_iff (hNM : N ≤r M) : N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE ↦ (heE (hR heR)).elim
/-
**Matroid.IsLoop.of_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, N.IsLoop e → N.IsRestriction M
 → M.IsLoop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsRestriction.isLoop_iff`：∀ {α : Type u_1} {M N : Matroid α} {e 
: α}, N.IsRestriction M → (N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e)
-/
lemma IsLoop.of_isRestriction (he : N.IsLoop e) (hNM : N ≤r M) : M.IsLoop e :=
  ((hNM.isLoop_iff).1 he).2
/-
**Matroid.IsLoop.isLoop_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`
。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, M.IsLoop e → N.IsRestriction M
 → e ∈ N.E → N.IsLoop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.IsRestriction.isLoop_iff`：∀ {α : Type u_1} {M N : Matroid α} {e 
: α}, N.IsRestriction M → (N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e)
-/
lemma IsLoop.isLoop_isRestriction (he : M.IsLoop e) (hNM : N ≤r M) (heN : e ∈ N.E) : N.IsLoop e :=
  (hNM.isLoop_iff).2 ⟨heN, he⟩

@[simp]
/-
**Matroid.map_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_loops {f : α -> β} {hf : InjOn f M.E} : (M.map f hf).loops = f '' M.lo
ops
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.map_closure_eq`：∀ {α : Type u_2} {β : Type u_3} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) (X : Set β),   (M.map f hf).closure X = f '' 
M.closure (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_loops {f : α → β} {hf : InjOn f M.E} : (M.map f hf).loops = f '' M.loops := by
  simp [loops]

@[simp]
/-
**Matroid.map_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：map_isLoop_iff {f : α -> β} {hf : InjOn f M.E} (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isLoop_iff`：isLoop_iff : M.IsLoop e ↔ e in M.loops
· 使用引理 `Matroid.map_loops`：map_loops {f : α -> β} {hf : InjOn f M.E} : (M.map f 
hf).loops = f '' M.loops
· 使用定理 `Set.InjOn.mem_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} 
{f : α → β} {x : α},   Set.InjOn f s → s₁ ⊆ s → x ∈ s → (f x ∈ f '' s₁ ↔ x ∈ s₁)
· 使用引理 `Matroid.loops_subset_ground`：loops_subset_ground (M : Matroid α) : M.loo
ps subseteq M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma map_isLoop_iff {f : α → β} {hf : InjOn f M.E} (he : e ∈ M.E := by aesop_mat) :
    (M.map f hf).IsLoop (f e) ↔ M.IsLoop e := by
  rw [isLoop_iff, map_loops, hf.mem_image_iff M.loops_subset_ground he, isLoop_iff]

@[simp]
/-
**Matroid.mapEmbedding_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mapEmbedding_isLoop_iff {f : α ↪ β} : (M.mapEmbedding f).IsLoop (f e) ↔ M.
IsLoop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.map_closure_eq`：∀ {α : Type u_2} {β : Type u_3} (M : Matroid α) 
(f : α → β) (hf : Set.InjOn f M.E) (X : Set β),   (M.map f hf).closure X = f '' 
M.closure (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapEmbedding_isLoop_iff {f : α ↪ β} : (M.mapEmbedding f).IsLoop (f e) ↔ M.IsLoop e := by
  simp [mapEmbedding, isLoop_iff, isLoop_iff, map_closure_eq, preimage_empty, ← closure_empty]

@[simp]
/-
**Matroid.comap_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comap_loops {M : Matroid β} {f : α -> β} : (M.comap f).loops = f ⁻¹' M.loo
ps
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.loops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.loops = M.closur
e ∅
· 使用定理 `Matroid.comap_closure_eq`：∀ {α : Type u_2} {β : Type u_3} (M : Matroid β
) (f : α → β) (X : Set α),   (M.comap f).closure X = f ⁻¹' M.closure (f '' X)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
lemma comap_loops {M : Matroid β} {f : α → β} : (M.comap f).loops = f ⁻¹' M.loops := by
  rw [loops, comap_closure_eq, image_empty, loops]

@[simp]
/-
**Matroid.comap_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comap_isLoop_iff {M : Matroid β} {f : α -> β} : (M.comap f).IsLoop e ↔ M.I
sLoop (f e)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.comap_loops`：comap_loops {M : Matroid β} {f : α -> β} : (M.comap
 f).loops = f ⁻¹' M.loops
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_isLoop_iff {M : Matroid β} {f : α → β} : (M.comap f).IsLoop e ↔ M.IsLoop (f e) := by
  simp [isLoop_iff]

@[simp]
/-
**Matroid.loopyOn_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e in E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.loopyOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.loo
pyOn E).closure X = E
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e ∈ E := by
  simp [isLoop_iff, loops]
/-
**Matroid.eq_loopyOn_iff_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eq_loopyOn_iff_loops {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E w
here mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.loops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.loops = M.closur
e ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.loopyOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.loo
pyOn E).closure X = E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_empty_eq_ground_iff`：closure_empty_eq_ground_iff : M.clo
sure ∅ = M.E ↔ M = loopyOn M.E
-/
lemma eq_loopyOn_iff_loops {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E where
  mp h := by rw [h, loops]; simp
  mpr | ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']
/-
**Matroid.restrict_subset_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_subset_loops_eq (hX : X subseteq M.loops) : M ↾ X = loopyOn X
参数：hX : X subseteq M.loops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eq_loopyOn_iff_loops`：eq_loopyOn_iff_loops {E : Set α} : M = loo
pyOn E ↔ M.loops = E ∧ M.E = E where mp h
· 使用引理 `Matroid.restrict_loops_eq'`：restrict_loops_eq' (M : Matroid α) (R : Set 
α) : (M ↾ R).loops = (M.loops inter R) union (R \ M.E)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
-/
lemma restrict_subset_loops_eq (hX : X ⊆ M.loops) : M ↾ X = loopyOn X := by
  rw [eq_loopyOn_iff_loops, restrict_loops_eq', inter_eq_self_of_subset_right hX,
    union_eq_self_of_subset_right sdiff_subset, and_iff_left M.restrict_ground_eq]

@[simp]
/-
**Matroid.freeOn_not_isLoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：freeOn_not_isLoop (E : Set α) (e : α) : ¬ (freeOn E).IsLoop e
参数：E : Set α；e : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.freeOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.free
On E).closure X = X ∩ E
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma freeOn_not_isLoop (E : Set α) (e : α) : ¬ (freeOn E).IsLoop e := by
  simp [isLoop_iff, loops]

@[simp]
/-
**Matroid.uniqueBaseOn_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_isLoop_iff {I E : Set α} : (uniqueBaseOn I E).IsLoop e ↔ e in
 E \ I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.uniqueBaseOn_closure_eq`：∀ {α : Type u_2} (I E X : Set α), (Matr
oid.uniqueBaseOn I E).closure X = X ∩ I ∩ E ∪ E \ I
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma uniqueBaseOn_isLoop_iff {I E : Set α} : (uniqueBaseOn I E).IsLoop e ↔ e ∈ E \ I := by
  simp [isLoop_iff, loops]
/-
**Matroid.eq_loopyOn_iff_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eq_loopyOn_iff_loops_eq {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = 
E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.loopyOn_closure_eq`：∀ {α : Type u_2} (E X : Set α), (Matroid.loo
pyOn E).closure X = E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.closure_empty_eq_ground_iff`：closure_empty_eq_ground_iff : M.clo
sure ∅ = M.E ↔ M = loopyOn M.E
· 使用定理 `Matroid.loops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.loops = M.closur
e ∅
-/
lemma eq_loopyOn_iff_loops_eq {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E :=
  ⟨fun h ↦ by simp [h, loops],
  fun ⟨h, h'⟩ ↦ by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

section IsNonloop

/-- `M.IsNonloop e` means that `e` is an element of `M.E` but not a loop of `M`. -/
@[mk_iff]
/-
**Matroid.IsNonloop** 是 Mathlib 中的一个结构，位于命名空间 `Matroid`。
形式化陈述：IsNonloop (M : Matroid α) (e : α) : Prop where not_isLoop : ¬ M.IsLoop e m
em_ground : e in M.E  attribute [aesop unsafe 20% (rule_sets
参数：M : Matroid α；e : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.IsNonloop e` means that `e` is an element of `M.E` but not a loop of `M`.
-/
structure IsNonloop (M : Matroid α) (e : α) : Prop where
  not_isLoop : ¬ M.IsLoop e
  mem_ground : e ∈ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsNonloop.mem_ground
/-
**Matroid.IsLoop.not_isNonloop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → ¬M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
-/
lemma IsLoop.not_isNonloop (he : M.IsLoop e) : ¬M.IsNonloop e :=
  fun h ↦ h.not_isLoop he
/-
**Matroid.compl_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：compl_loops_eq (M : Matroid α) : M.E \ M.loops = {e | M.IsNonloop e}
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma compl_loops_eq (M : Matroid α) : M.E \ M.loops = {e | M.IsNonloop e} := by
  simp [Set.ext_iff, isNonloop_iff, and_comm, isLoop_iff]
/-
**Matroid.isNonloop_of_not_isLoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_of_not_isLoop (he : e in M.E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNonloop_of_not_isLoop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsLoop e) : M.IsNonloop e :=
  ⟨h,he⟩
/-
**Matroid.isLoop_of_not_isNonloop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isLoop_of_not_isNonloop (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.isNonloop_iff`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsNon
loop e ↔ ¬M.IsLoop e ∧ e ∈ M.E
-/
lemma isLoop_of_not_isNonloop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsNonloop e) :
    M.IsLoop e := by
  rwa [isNonloop_iff, and_iff_left he, not_not] at h

@[simp]
/-
**Matroid.not_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：not_isLoop_iff (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
-/
lemma not_isLoop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsLoop e ↔ M.IsNonloop e :=
  ⟨fun h ↦ ⟨h, he⟩, IsNonloop.not_isLoop⟩

@[simp]
/-
**Matroid.not_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：not_isNonloop_iff (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.not_isLoop_iff`：not_isLoop_iff (he : e in M.E
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma not_isNonloop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsNonloop e ↔ M.IsLoop e := by
  rw [← not_isLoop_iff, not_not]
/-
**Matroid.isNonloop_iff_mem_compl_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e in M.E \ M.loops
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isNonloop_iff`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsNon
loop e ↔ ¬M.IsLoop e ∧ e ∈ M.E
· 使用定理 `Matroid.IsLoop.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsLoop 
e = (e ∈ M.loops)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e ∈ M.E \ M.loops := by
  rw [isNonloop_iff, IsLoop, and_comm, mem_sdiff]
/-
**Matroid.setOfPred_isNonloop_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：setOfPred_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.loo
ps
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Matroid.isNonloop_iff_mem_compl_loops`：isNonloop_iff_mem_compl_loops : M
.IsNonloop e ↔ e in M.E \ M.loops
-/
lemma setOfPred_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.loops :=
  Set.ext (fun _ ↦ isNonloop_iff_mem_compl_loops)

@[deprecated (since := "2026-07-09")]
alias setOf_isNonloop_eq := setOfPred_isNonloop_eq
/-
**Matroid.not_isNonloop_iff_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.loops
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matroid.IsNonloop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → e ∈ M.E
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_inter_eq_empty`：singleton_inter_eq_empty : {a} inter s = ∅
 ↔ a ∉ s
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.loops := by
  by_cases he : e ∈ M.E
  · simp [isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he, loops,
    (show ¬ M.IsNonloop e from fun h ↦ he h.mem_ground)]
/-
**Matroid.isLoop_or_isNonloop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isLoop_or_isNonloop (M : Matroid α) (e : α) (he : e in M.E
参数：M : Matroid α；e : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isNonloop_iff`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsNon
loop e ↔ ¬M.IsLoop e ∧ e ∈ M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma isLoop_or_isNonloop (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ∨ M.IsNonloop e := by
  rw [isNonloop_iff, and_iff_left he]; apply em

@[simp]
/-
**Matroid.indep_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isNonloop_iff`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsNon
loop e ↔ ¬M.IsLoop e ∧ e ∈ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.singleton_dep`：singleton_dep : M.Dep {e} ↔ M.IsLoop e
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma indep_singleton : M.Indep {e} ↔ M.IsNonloop e := by
  rw [isNonloop_iff, ← singleton_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton
/-
**Matroid.Indep.isNonloop_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {I : Set α}, M.Indep I → e ∈ I → 
M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.not_isLoop_iff`：not_isLoop_iff (he : e in M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsLoop.notMem_of_indep`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.IsLoop e → M.Indep I → e ∉ I
-/
lemma Indep.isNonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.IsNonloop e := by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he ↦ (he.notMem_of_indep hI) h
/-
**Matroid.IsNonloop.exists_mem_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonlo
op`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsNonloop e → ∃ B, M.IsBase B 
∧ e ∈ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
-/
lemma IsNonloop.exists_mem_isBase (he : M.IsNonloop e) : ∃ B, M.IsBase B ∧ e ∈ B := by
  simpa using (indep_singleton.2 he).exists_isBase_superset
/-
**Matroid.IsCocircuit.isNonloop_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCoci
rcuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {K : Set α}, M.IsCocircuit K → e 
∈ K → M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.not_isLoop_iff`：not_isLoop_iff (he : e in M.E
· 使用定理 `Matroid.IsCocircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C :
 Set α}, M.IsCocircuit C → C ⊆ M.E
· 使用引理 `Matroid.singleton_isCircuit`：singleton_isCircuit : M.IsCircuit {e} ↔ M.I
sLoop e
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用定理 `Matroid.IsCircuit.isCocircuit_inter_nontrivial`：∀ {α : Type u_1} {M : Ma
troid α} {C K : Set α}, M.IsCircuit C → M.IsCocircuit K → (C ∩ K).Nonempty → (C 
∩ K).Nontrivial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_inter_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ {a} ∩ s = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCocircuit.isNonloop_of_mem {K : Set α} (hK : M.IsCocircuit K) (he : e ∈ K) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff (hK.subset_ground he), ← singleton_isCircuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.isCocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl
/-
**Matroid.IsCircuit.isNonloop_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircui
t`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α}, M.IsCircuit C → C.No
ntrivial → e ∈ C → M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.isNonloop_of_not_isLoop`：isNonloop_of_not_isLoop (he : e in M.E
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsLoop.eq_of_isCircuit_mem`：∀ {α : Type u_1} {M : Matroid α} {e 
: α} {C : Set α}, M.IsLoop e → M.IsCircuit C → e ∈ C → C = {e}
-/
lemma IsCircuit.isNonloop_of_mem (hC : M.IsCircuit C) (hC' : C.Nontrivial) (he : e ∈ C) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop (hC.subset_ground he)
    (fun hL ↦ by simp [hL.eq_of_isCircuit_mem hC he] at hC')
/-
**Matroid.IsCircuit.isNonloop_of_mem_of_one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α}, M.IsCircuit C → 1 < 
C.encard → e ∈ C → M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.isNonloop_of_not_isLoop`：isNonloop_of_not_isLoop (he : e in M.E
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Matroid.IsLoop.eq_of_isCircuit_mem`：∀ {α : Type u_1} {M : Matroid α} {e 
: α} {C : Set α}, M.IsLoop e → M.IsCircuit C → e ∈ C → C = {e}
-/
lemma IsCircuit.isNonloop_of_mem_of_one_lt_card (hC : M.IsCircuit C) (h : 1 < C.encard)
    (he : e ∈ C) : M.IsNonloop e := by
  refine isNonloop_of_not_isLoop (hC.subset_ground he) (fun hlp ↦ ?_)
  rw [hlp.eq_of_isCircuit_mem hC he, encard_singleton] at h
  exact h.ne rfl
/-
**Matroid.isNonloop_of_notMem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_of_notMem_closure (h : e ∉ M.closure X) (he : e in M.E
参数：h : e ∉ M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.isNonloop_of_not_isLoop`：isNonloop_of_not_isLoop (he : e in M.E
· 使用定理 `Matroid.IsLoop.mem_closure`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.
IsLoop e → ∀ (X : Set α), e ∈ M.closure X
-/
lemma isNonloop_of_notMem_closure (h : e ∉ M.closure X) (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop he (fun hel ↦ h (hel.mem_closure X))
/-
**Matroid.isNonloop_iff_notMem_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_iff_notMem_loops (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isNonloop_iff`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsNon
loop e ↔ ¬M.IsLoop e ∧ e ∈ M.E
· 使用引理 `Matroid.isLoop_iff`：isLoop_iff : M.IsLoop e ↔ e in M.loops
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isNonloop_iff_notMem_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e ↔ e ∉ M.loops := by
  rw [isNonloop_iff, isLoop_iff, and_iff_left he]
/-
**Matroid.IsNonloop.mem_closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsN
onloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α}, M.IsNonloop e → e ∈ M.closure 
{f} → f ∈ M.closure {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Matroid.closure_exchange`：closure_exchange (he : e in M.closure (insert 
f X) \ M.closure X) : f in M.closure (insert e X) \ M.closure X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isNonloop_iff_notMem_loops`：isNonloop_iff_notMem_loops (he : e i
n M.E
· 使用定理 `Matroid.IsNonloop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → e ∈ M.E
-/
lemma IsNonloop.mem_closure_singleton (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    f ∈ M.closure {e} := by
  rw [← union_empty {_}, singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_notMem_loops he.mem_ground).1 he⟩).1
/-
**Matroid.IsNonloop.mem_closure_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloo
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α}, M.IsNonloop e → M.IsNonloop f 
→ (f ∈ M.closure {e} ↔ e ∈ M.closure {f})
参数：f ∈ M.closure {e} ↔ e ∈ M.closure {f}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.mem_closure_singleton`：∀ {α : Type u_1} {M : Matroid α
} {e f : α}, M.IsNonloop e → e ∈ M.closure {f} → f ∈ M.closure {e}
-/
lemma IsNonloop.mem_closure_comm (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    f ∈ M.closure {e} ↔ e ∈ M.closure {f} :=
  ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩
/-
**Matroid.IsNonloop.isNonloop_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α}, M.IsNonloop e → e ∈ M.closure 
{f} → M.IsNonloop f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isNonloop_iff`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsNon
loop e ↔ ¬M.IsLoop e ∧ e ∈ M.E
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
· 使用引理 `Matroid.isLoop_iff`：isLoop_iff : M.IsLoop e ↔ e in M.loops
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Matroid.closure_loops`：closure_loops (M : Matroid α) : M.closure M.loops
 = M.loops
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Matroid.closure_insert_congr_right`：closure_insert_congr_right (h : M.cl
osure X = M.closure Y) : M.closure (insert e X) = M.closure (insert e Y)
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_singleton_eq_empty`：inter_singleton_eq_empty : s inter {a} = ∅
 ↔ a ∉ s
· 使用定理 `Matroid.loops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.loops = M.closur
e ∅
-/
lemma IsNonloop.isNonloop_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.IsNonloop f := by
  rw [isNonloop_iff, and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff] at *; convert! hef using 1
  obtain (hf | hf) := em (f ∈ M.E)
  · rw [← closure_loops, ← insert_eq_of_mem (h hf), closure_insert_congr_right M.closure_loops,
      insert_empty_eq]
  rw [eq_comm, ← closure_inter_ground, inter_comm, inter_singleton_eq_empty.mpr hf, loops]
/-
**Matroid.IsNonloop.closure_eq_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α}, M.IsNonloop e → e ∈ M.closure 
{f} → M.closure {e} = M.closure {f}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_closure`：∀ {α : Type u_2} (M : Matroid α) (X : Set α), M
.closure (M.closure X) = M.closure X
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Matroid.closure_insert_closure_eq_closure_insert`：∀ {α : Type u_2} (M : 
Matroid α) (e : α) (X : Set α), M.closure (insert e (M.closure X)) = M.closure (
insert e X)
· 使用定理 `Matroid.IsNonloop.mem_closure_singleton`：∀ {α : Type u_1} {M : Matroid α
} {e f : α}, M.IsNonloop e → e ∈ M.closure {f} → f ∈ M.closure {e}
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
-/
lemma IsNonloop.closure_eq_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.closure {e} = M.closure {f} := by
  rw [← closure_closure _ {f}, ← insert_eq_of_mem hef, closure_insert_closure_eq_closure_insert,
    ← closure_closure _ {e}, ← insert_eq_of_mem (he.mem_closure_singleton hef),
    closure_insert_closure_eq_closure_insert, pair_comm]

/-- Two distinct nonloops with the same closure form a circuit. -/
/-
**Matroid.IsNonloop.closure_eq_closure_iff_isCircuit_of_ne** 是 Mathlib 中的一个定理，位于
命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α}, M.IsNonloop e → e ≠ f → (M.clo
sure {e} = M.closure {f} ↔ M.IsCircuit {e, f})
参数：M.closure {e} = M.closure {f} ↔ M.IsCircuit {e, f}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.isNonloop_of_mem_closure`：∀ {α : Type u_1} {M : Matroi
d α} {e f : α}, M.IsNonloop e → e ∈ M.closure {f} → M.IsNonloop f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.mem_closure_self`：mem_closure_self (M : Matroid α) (e : α) (he :
 e in M.E
· 使用定理 `Matroid.IsNonloop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → e ∈ M.E
· 使用引理 `Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep`：isCircuit_iff_de
p_forall_sdiff_singleton_indep : M.IsCircuit C ↔ M.Dep C ∧ forall e in C, M.Inde
p (C \ {e})
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.insert_indep_iff_of_notMem`：∀ {α : Type u_2} {M : Matroid 
α} {e : α} {I : Set α}, M.Indep I → e ∉ I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.
closure I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.pair_sdiff_left`：pair_sdiff_left (hab : a != b) : ({a, b} : Set α) \
 {a} = {b}
· 使用引理 `Set.pair_sdiff_right`：pair_sdiff_right (hab : a != b) : ({a, b} : Set α)
 \ {b} = {a}
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matroid.IsCircuit.closure_sdiff_singleton_eq`：∀ {α : Type u_1} {M : Matr
oid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), M.closure (C \ {e}) = M.closure C
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
Two distinct nonloops with the same closure form a circuit.
-/
lemma IsNonloop.closure_eq_closure_iff_isCircuit_of_ne (he : M.IsNonloop e) (hef : e ≠ f) :
    M.closure {e} = M.closure {f} ↔ M.IsCircuit {e, f} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hf := he.isNonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [isCircuit_iff_dep_forall_sdiff_singleton_indep, dep_iff, insert_subset_iff,
      and_iff_right he.mem_ground, singleton_subset_iff, and_iff_left hf.mem_ground]
    suffices ¬ M.Indep {e, f} by simpa [pair_sdiff_left hef, hf, pair_sdiff_right hef, he]
    rw [Indep.insert_indep_iff_of_notMem (by simpa) (by simpa)]
    simp [← h, mem_closure_self _ _ he.mem_ground]
  have hclosure := (h.closure_sdiff_singleton_eq e).trans
    (h.closure_sdiff_singleton_eq f).symm
  rwa [pair_sdiff_left hef, pair_sdiff_right hef, eq_comm] at hclosure
/-
**Matroid.IsNonloop.closure_eq_closure_iff_eq_or_dep** 是 Mathlib 中的一个定理，位于命名空间 `
Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α},   M.IsNonloop e → M.IsNonloop 
f → (M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f})
参数：M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsNonloop.closure_eq_closure_iff_isCircuit_of_ne`：∀ {α : Type u_
1} {M : Matroid α} {e f : α}, M.IsNonloop e → e ≠ f → (M.closure {e} = M.closure
 {f} ↔ M.IsCircuit {e, f})
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.IsNonloop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → e ∈ M.E
· 使用引理 `Set.pair_sdiff_left`：pair_sdiff_left (hab : a != b) : ({a, b} : Set α) \
 {a} = {b}
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用引理 `Set.pair_sdiff_right`：pair_sdiff_right (hab : a != b) : ({a, b} : Set α)
 \ {b} = {a}
-/
lemma IsNonloop.closure_eq_closure_iff_eq_or_dep (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_isCircuit_of_ne hne, or_iff_right hne,
    isCircuit_iff_dep_forall_sdiff_singleton_indep, dep_iff, insert_subset_iff,
    singleton_subset_iff, and_iff_left hf.mem_ground, and_iff_left he.mem_ground,
    and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_sdiff_left hne, indep_singleton]
  rwa [pair_sdiff_right hne, indep_singleton]
/-
**Matroid.exists_isNonloop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：exists_isNonloop (M : Matroid α) [RankPos M] : exists e, M.IsNonloop e
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.IsBase.nonempty`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M
.RankPos], M.IsBase B → B.Nonempty
· 使用定理 `Matroid.Indep.isNonloop_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → e ∈ I → M.IsNonloop e
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
-/
lemma exists_isNonloop (M : Matroid α) [RankPos M] : ∃ e, M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  ⟨_, hB.indep.isNonloop_of_mem hB.nonempty.some_mem⟩
/-
**Matroid.IsNonloop.rankPos** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsNonloop e → M.RankPos
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.rankPos_of_nonempty`：∀ {α : Type u_1} {M : Matroid α} {I :
 Set α}, M.Indep I → I.Nonempty → M.RankPos
· 使用定理 `Matroid.IsNonloop.indep`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsN
onloop e → M.Indep {e}
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
-/
lemma IsNonloop.rankPos (h : M.IsNonloop e) : M.RankPos :=
  h.indep.rankPos_of_nonempty (singleton_nonempty e)

@[simp]
/-
**Matroid.restrict_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_isNonloop_iff {R : Set α} : (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧
 e in R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_isNonloop_iff {R : Set α} : (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e ∈ R := by
  rw [← indep_singleton, restrict_indep_iff, singleton_subset_iff, indep_singleton]
/-
**Matroid.IsNonloop.of_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {R : Set α}, (M.restrict R).IsNon
loop e → M.IsNonloop e
参数：M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.restrict_isNonloop_iff`：restrict_isNonloop_iff {R : Set α} : (M 
↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e in R
-/
lemma IsNonloop.of_restrict {R : Set α} (h : (M ↾ R).IsNonloop e) : M.IsNonloop e :=
  (restrict_isNonloop_iff.1 h).1
/-
**Matroid.IsNonloop.of_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloo
p`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, N.IsNonloop e → N.IsRestrictio
n M → M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.of_restrict`：∀ {α : Type u_1} {M : Matroid α} {e : α} 
{R : Set α}, (M.restrict R).IsNonloop e → M.IsNonloop e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsNonloop.of_isRestriction (h : N.IsNonloop e) (hNM : N ≤r M) : M.IsNonloop e := by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict
/-
**Matroid.isNonloop_iff_restrict_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_iff_restrict_of_mem {R : Set α} (he : e in R) : M.IsNonloop e ↔ 
(M ↾ R).IsNonloop e
参数：he : e in R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.restrict_isNonloop_iff`：restrict_isNonloop_iff {R : Set α} : (M 
↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e in R
· 使用定理 `Matroid.IsNonloop.of_restrict`：∀ {α : Type u_1} {M : Matroid α} {e : α} 
{R : Set α}, (M.restrict R).IsNonloop e → M.IsNonloop e
-/
lemma isNonloop_iff_restrict_of_mem {R : Set α} (he : e ∈ R) :
    M.IsNonloop e ↔ (M ↾ R).IsNonloop e :=
  ⟨fun h ↦ restrict_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_restrict⟩

@[simp]
/-
**Matroid.comap_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：comap_isNonloop_iff {M : Matroid β} {f : α -> β} : (M.comap f).IsNonloop e
 ↔ M.IsNonloop (f e)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用定理 `Matroid.comap_indep_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {I 
: Set α} {N : Matroid β},   (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ Set.InjOn f
 I
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.injOn_singleton`：injOn_singleton (f : α -> β) (a : α) : InjOn f {a}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comap_isNonloop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).IsNonloop e ↔ M.IsNonloop (f e) := by
  rw [← indep_singleton, comap_indep_iff, image_singleton, indep_singleton,
    and_iff_left (injOn_singleton _ _)]

@[simp]
/-
**Matroid.freeOn_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：freeOn_isNonloop_iff {E : Set α} : (freeOn E).IsNonloop e ↔ e in E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用定理 `Matroid.freeOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.freeO
n E).Indep I ↔ I ⊆ E
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma freeOn_isNonloop_iff {E : Set α} : (freeOn E).IsNonloop e ↔ e ∈ E := by
  rw [← indep_singleton, freeOn_indep_iff, singleton_subset_iff]

@[simp]
/-
**Matroid.uniqueBaseOn_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_isNonloop_iff {I E : Set α} : (uniqueBaseOn I E).IsNonloop e 
↔ e in I inter E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用定理 `Matroid.uniqueBaseOn_indep_iff'`：∀ {α : Type u_1} {E I J : Set α}, (Matr
oid.uniqueBaseOn I E).Indep J ↔ J ⊆ I ∩ E
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma uniqueBaseOn_isNonloop_iff {I E : Set α} :
    (uniqueBaseOn I E).IsNonloop e ↔ e ∈ I ∩ E := by
  rw [← indep_singleton, uniqueBaseOn_indep_iff', singleton_subset_iff]
/-
**Matroid.IsNonloop.exists_mem_isCocircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Nonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsNonloop e → ∃ K, M.IsCocircu
it K ∧ e ∈ K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.exists_mem_isBase`：∀ {α : Type u_1} {M : Matroid α} {e
 : α}, M.IsNonloop e → ∃ B, M.IsBase B ∧ e ∈ B
· 使用引理 `Matroid.fundCocircuit_isCocircuit`：fundCocircuit_isCocircuit (he : e in 
B) (hB : M.IsBase B) : M.IsCocircuit M.fundCocircuit e B
· 使用引理 `Matroid.mem_fundCocircuit`：mem_fundCocircuit (M : Matroid α) (e : α) (B 
: Set α) : e in M.fundCocircuit e B
-/
lemma IsNonloop.exists_mem_isCocircuit (he : M.IsNonloop e) : ∃ K, M.IsCocircuit K ∧ e ∈ K := by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]
/-
**Matroid.closure_inter_setOfPred_isNonloop_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroi
d`。
形式化陈述：closure_inter_setOfPred_isNonloop_eq (M : Matroid α) (X : Set α) : M.closu
re (X inter {e | M.IsNonloop e}) = M.closure X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.setOfPred_isNonloop_eq`：setOfPred_isNonloop_eq (M : Matroid α) :
 {e | M.IsNonloop e} = M.E \ M.loops
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `Matroid.closure_sdiff_loops_eq`：∀ {α : Type u_1} (M : Matroid α) (X : Se
t α), M.closure (X \ M.loops) = M.closure X
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
-/
lemma closure_inter_setOfPred_isNonloop_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∩ {e | M.IsNonloop e}) = M.closure X := by
  rw [setOfPred_isNonloop_eq, ← inter_sdiff_assoc, closure_sdiff_loops_eq, closure_inter_ground]

@[deprecated (since := "2026-07-09")]
alias closure_inter_setOf_isNonloop_eq := closure_inter_setOfPred_isNonloop_eq

end IsNonloop

section IsColoop

variable {B K : Set α}

/-- A coloop is a loop of the dual matroid.
See `Matroid.isColoop_tfae` for a number of equivalent definitions. -/
/-
**Matroid.IsColoop** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsColoop (M : Matroid α) (e : α) : Prop
参数：M : Matroid α；e : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coloop is a loop of the dual matroid.
See `Matroid.isColoop_tfae` for a number of equivalent definitions.
-/
def IsColoop (M : Matroid α) (e : α) : Prop := M✶.IsLoop e

/-- `M.coloops` is the set of coloops of `M`. -/
/-
**Matroid.coloops** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：coloops (M : Matroid α)
参数：M : Matroid α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.coloops` is the set of coloops of `M`.
-/
def coloops (M : Matroid α) := M✶.loops

@[aesop unsafe 20% (rule_sets := [Matroid])]
/-
**Matroid.IsColoop.mem_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsColoop e → e ∈ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.I
sLoop e → e ∈ M.E
-/
lemma IsColoop.mem_ground (he : M.IsColoop e) : e ∈ M.E :=
  @IsLoop.mem_ground α (M✶) e he

@[aesop unsafe 20% (rule_sets := [Matroid])]
/-
**Matroid.coloops_subset_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：coloops_subset_ground (M : Matroid α) : M.coloops subseteq M.E
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsColoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M
.IsColoop e → e ∈ M.E
-/
lemma coloops_subset_ground (M : Matroid α) : M.coloops ⊆ M.E :=
  fun _ ↦ IsColoop.mem_ground
/-
**Matroid.isColoop_iff_mem_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isColoop_iff_mem_coloops : M.IsColoop e ↔ e in M.coloops
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isColoop_iff_mem_coloops : M.IsColoop e ↔ e ∈ M.coloops := Iff.rfl

@[simp]
/-
**Matroid.dual_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_loops : M✶.loops = M.coloops
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dual_loops : M✶.loops = M.coloops := rfl

@[simp]
/-
**Matroid.dual_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_coloops : M✶.coloops = M.loops
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.coloops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.coloops = M✶.l
oops
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
lemma dual_coloops : M✶.coloops = M.loops := by
  rw [coloops, dual_dual]
/-
**Matroid.IsColoop.dual_isLoop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsColoop e → M✶.IsLoop e
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsColoop.dual_isLoop (he : M.IsColoop e) : M✶.IsLoop e :=
  he
/-
**Matroid.IsColoop.isCocircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsColoop e → M.IsCocircuit {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.Is
Loop e → M.IsCircuit {e}
-/
lemma IsColoop.isCocircuit (he : M.IsColoop e) : M.IsCocircuit {e} :=
  IsLoop.isCircuit he
/-
**Matroid.IsLoop.dual_isColoop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → M✶.IsColoop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsColoop.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsCol
oop e = M✶.IsLoop e
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
lemma IsLoop.dual_isColoop (he : M.IsLoop e) : M✶.IsColoop e := by rwa [IsColoop, dual_dual]

@[simp]
/-
**Matroid.dual_isColoop_iff_isLoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_isColoop_iff_isLoop : M✶.IsColoop e ↔ M.IsLoop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Matroid.IsColoop.dual_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsColoop e → M✶.IsLoop e
· 使用定理 `Matroid.IsLoop.dual_isColoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsLoop e → M✶.IsColoop e
-/
lemma dual_isColoop_iff_isLoop : M✶.IsColoop e ↔ M.IsLoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_isColoop⟩

@[simp]
/-
**Matroid.dual_isLoop_iff_isColoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_isLoop_iff_isColoop : M✶.IsLoop e ↔ M.IsColoop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Matroid.IsLoop.dual_isColoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsLoop e → M✶.IsColoop e
· 使用定理 `Matroid.IsColoop.dual_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsColoop e → M✶.IsLoop e
-/
lemma dual_isLoop_iff_isColoop : M✶.IsLoop e ↔ M.IsColoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isColoop, IsColoop.dual_isLoop⟩
/-
**Matroid.singleton_isCocircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：singleton_isCocircuit : M.IsCocircuit {e} ↔ M.IsColoop e
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
lemma singleton_isCocircuit : M.IsCocircuit {e} ↔ M.IsColoop e := by
  simp
/-
**Matroid.isColoop_tfae** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isColoop_tfae (M : Matroid α) (e : α) : List.TFAE [ M.IsColoop e, e in M.c
oloops, M.IsCocircuit {e}, forall ⦃B⦄, M.IsBase B -> e in B, (forall ⦃C⦄, M.IsCi
rcuit C -> e ∉ C) ∧ e in M.E, forall X, e in M.closure X ↔ e in X, ¬ M.Spanning 
(M.E \ {e}) ]
参数：M : Matroid α；e : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Matroid.singleton_isCocircuit`：singleton_isCocircuit : M.IsCocircuit {e}
 ↔ M.IsColoop e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `Matroid.IsBase.compl_isBase_dual`：∀ {α : Type u_1} {M : Matroid α} {B : 
Set α}, M.IsBase B → M✶.IsBase (M.E \ B)
· 使用定理 `Matroid.IsBase.compl_isBase_of_dual`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M✶.IsBase B → M.IsBase (M.E \ B)
· 使用定理 `Matroid.IsCircuit.inter_isCocircuit_ne_singleton`：∀ {α : Type u_1} {M : 
Matroid α} {C : Set α} {e : α} {K : Set α}, M.IsCircuit C → M.IsCocircuit K → C 
∩ K ≠ {e}
· 使用定理 `Matroid.IsCocircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C :
 Set α}, M.IsCocircuit C → C ⊆ M.E
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.mem_closure_iff_exists_isCircuit`：mem_closure_iff_exists_isCircu
it (he : e ∉ X) : e in M.closure X ↔ exists C subseteq insert e X, M.IsCircuit C
 ∧ e in C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem`：∀ {α : Type u_1} {
M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → e ∈ M.closure (C \ {
e})
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Matroid.spanning_iff_compl_coindep`：spanning_iff_compl_coindep (hS : S s
ubseteq M.E
（共 43 条，此处仅展示前 30 条）
-/
lemma isColoop_tfae (M : Matroid α) (e : α) : List.TFAE [
    M.IsColoop e,
    e ∈ M.coloops,
    M.IsCocircuit {e},
    ∀ ⦃B⦄, M.IsBase B → e ∈ B,
    (∀ ⦃C⦄, M.IsCircuit C → e ∉ C) ∧ e ∈ M.E,
    ∀ X, e ∈ M.closure X ↔ e ∈ X,
    ¬ M.Spanning (M.E \ {e}) ] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 1 ↔ 3 := singleton_isCocircuit.symm
  tfae_have 1 ↔ 4 := by
    simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase]
    refine ⟨fun h B hB ↦ ?_, fun h B hB ↦ h hB.compl_isBase_of_dual⟩
    obtain ⟨-, heB : e ∈ B⟩ := by simpa using h (M.E \ B) hB.compl_isBase_dual
    assumption
  tfae_have 3 → 5 := fun h ↦
    ⟨fun C hC heC ↦ hC.inter_isCocircuit_ne_singleton h (e := e) (by simpa), h.subset_ground rfl⟩
  tfae_have 5 → 4 := by
    refine fun ⟨h, heE⟩ B hB ↦ by_contra fun heB ↦ ?_
    rw [← hB.closure_eq] at heE
    obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heB).1 heE
    exact h hC heC
  tfae_have 5 ↔ 6 := by
    refine ⟨fun h X ↦ ⟨fun heX ↦ by_contra fun heX' ↦ ?_, fun heX ↦ M.mem_closure_of_mem' heX h.2⟩,
      fun h ↦ ⟨fun C hC heC ↦ ?_, M.closure_subset_ground _ <| (h {e}).2 rfl⟩⟩
    · obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heX').1 heX
      exact h.1 hC heC
    · simpa [hC.mem_closure_sdiff_singleton_of_mem heC] using h (C \ {e})
  tfae_have 1 ↔ 7 := by
    wlog he : e ∈ M.E
    · exact iff_of_false (fun h ↦ he h.mem_ground) <| by simp [he, M.ground_spanning]
    rw [spanning_iff_compl_coindep sdiff_subset, ← dual_isLoop_iff_isColoop, ← singleton_dep,
      sdiff_sdiff_cancel_left (by simpa), ← not_indep_iff (by simpa)]
  tfae_finish
/-
**Matroid.isColoop_iff_forall_mem_isBase** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isColoop_iff_forall_mem_isBase : M.IsColoop e ↔ forall ⦃B⦄, M.IsBase B -> 
e in B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isColoop_tfae`：isColoop_tfae (M : Matroid α) (e : α) : List.TFAE
 [ M.IsColoop e, e in M.coloops, M.IsCocircuit {e}, forall ⦃B⦄, M.IsBase B -> e 
in B, (fora…
-/
lemma isColoop_iff_forall_mem_isBase : M.IsColoop e ↔ ∀ ⦃B⦄, M.IsBase B → e ∈ B :=
  (M.isColoop_tfae e).out 0 3
/-
**Matroid.IsBase.mem_of_isColoop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {B : Set α}, M.IsBase B → M.IsCol
oop e → e ∈ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isColoop_iff_forall_mem_isBase`：isColoop_iff_forall_mem_isBase :
 M.IsColoop e ↔ forall ⦃B⦄, M.IsBase B -> e in B
-/
lemma IsBase.mem_of_isColoop (hB : M.IsBase B) (he : M.IsColoop e) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB
/-
**Matroid.IsColoop.mem_of_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {B : Set α}, M.IsColoop e → M.IsB
ase B → e ∈ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isColoop_iff_forall_mem_isBase`：isColoop_iff_forall_mem_isBase :
 M.IsColoop e ↔ forall ⦃B⦄, M.IsBase B -> e in B
-/
lemma IsColoop.mem_of_isBase (he : M.IsColoop e) (hB : M.IsBase B) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB
/-
**Matroid.IsBase.coloops_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → M.coloops ⊆ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsColoop.mem_of_isBase`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {B : Set α}, M.IsColoop e → M.IsBase B → e ∈ B
-/
lemma IsBase.coloops_subset (hB : M.IsBase B) : M.coloops ⊆ B :=
  fun _ he ↦ IsColoop.mem_of_isBase he hB
/-
**Matroid.IsColoop.isNonloop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsColoop e → M.IsNonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.Indep.isNonloop_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → e ∈ I → M.IsNonloop e
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isColoop_iff_forall_mem_isBase`：isColoop_iff_forall_mem_isBase :
 M.IsColoop e ↔ forall ⦃B⦄, M.IsBase B -> e in B
-/
lemma IsColoop.isNonloop (h : M.IsColoop e) : M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((isColoop_iff_forall_mem_isBase.mp h) hB)
/-
**Matroid.IsLoop.not_isColoop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → ¬M.IsColoop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_isLoop_iff_isColoop`：dual_isLoop_iff_isColoop : M✶.IsLoop e
 ↔ M.IsColoop e
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
· 使用定理 `Matroid.IsColoop.isNonloop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.
IsColoop e → M.IsNonloop e
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
lemma IsLoop.not_isColoop (h : M.IsLoop e) : ¬M.IsColoop e := by
  rw [← dual_isLoop_iff_isColoop]; rw [← dual_dual M, dual_isLoop_iff_isColoop] at h
  exact h.isNonloop.not_isLoop
/-
**Matroid.IsColoop.notMem_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoop`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α}, M.IsColoop e → M.IsC
ircuit C → e ∉ C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
· 使用定理 `Matroid.IsCocircuit.isNonloop_of_mem`：∀ {α : Type u_1} {M : Matroid α} {
e : α} {K : Set α}, M.IsCocircuit K → e ∈ K → M.IsNonloop e
· 使用定理 `Matroid.IsCircuit.isCocircuit`：∀ {α : Type u_1} {M : Matroid α} {C : Set
 α}, M.IsCircuit C → M✶.IsCocircuit C
-/
lemma IsColoop.notMem_isCircuit (he : M.IsColoop e) (hC : M.IsCircuit C) : e ∉ C :=
  fun h ↦ (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he
/-
**Matroid.IsCircuit.disjoint_coloops** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircui
t`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → Disjoint C M
.coloops
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Matroid.IsColoop.notMem_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {e :
 α} {C : Set α}, M.IsColoop e → M.IsCircuit C → e ∉ C
-/
lemma IsCircuit.disjoint_coloops (hC : M.IsCircuit C) : Disjoint C M.coloops :=
  disjoint_right.2 <| fun _ he ↦ IsColoop.notMem_isCircuit he hC
/-
**Matroid.isColoop_iff_forall_notMem_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroi
d`。
形式化陈述：isColoop_iff_forall_notMem_isCircuit (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isColoop_tfae`：isColoop_tfae (M : Matroid α) (e : α) : List.TFAE
 [ M.IsColoop e, e in M.coloops, M.IsCocircuit {e}, forall ⦃B⦄, M.IsBase B -> e 
in B, (fora…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isColoop_iff_forall_notMem_isCircuit (he : e ∈ M.E := by aesop_mat) :
    M.IsColoop e ↔ ∀ ⦃C⦄, M.IsCircuit C → e ∉ C := by
  simp_rw [(M.isColoop_tfae e).out 0 4, and_iff_left he]
/-
**Matroid.isColoop_iff_forall_mem_compl_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Mat
roid`。
形式化陈述：isColoop_iff_forall_mem_compl_isCircuit [RankPos M✶] : M.IsColoop e ↔ fora
ll C, M.IsCircuit C -> e in M.E \ C
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Matroid.exists_isCircuit`：exists_isCircuit [RankPos M✶] : exists C, M.Is
Circuit C
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.IsColoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M
.IsColoop e → e ∈ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isColoop_iff_forall_mem_compl_isCircuit [RankPos M✶] :
    M.IsColoop e ↔ ∀ C, M.IsCircuit C → e ∈ M.E \ C := by
  by_cases he : e ∈ M.E
  · simp [isColoop_iff_forall_notMem_isCircuit, he]
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  exact iff_of_false (fun h ↦ he h.mem_ground) fun h ↦ he (h C hC).1
/-
**Matroid.IsCircuit.not_isColoop_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCir
cuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α}, M.IsCircuit C → e ∈ 
C → ¬M.IsColoop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsColoop.notMem_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {e :
 α} {C : Set α}, M.IsColoop e → M.IsCircuit C → e ∉ C
-/
lemma IsCircuit.not_isColoop_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) : ¬ M.IsColoop e :=
  fun h ↦ h.notMem_isCircuit hC heC
/-
**Matroid.isColoop_iff_forall_mem_closure_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Mat
roid`。
形式化陈述：isColoop_iff_forall_mem_closure_iff_mem : M.IsColoop e ↔ (forall X, e in M
.closure X ↔ e in X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isColoop_tfae`：isColoop_tfae (M : Matroid α) (e : α) : List.TFAE
 [ M.IsColoop e, e in M.coloops, M.IsCocircuit {e}, forall ⦃B⦄, M.IsBase B -> e 
in B, (fora…
-/
lemma isColoop_iff_forall_mem_closure_iff_mem : M.IsColoop e ↔ (∀ X, e ∈ M.closure X ↔ e ∈ X) :=
  (M.isColoop_tfae e).out 0 5

/-- A version of `Matroid.isColoop_iff_forall_mem_closure_iff_mem` where we only quantify
over subsets of the ground set. -/
/-
**Matroid.isColoop_iff_forall_mem_closure_iff_mem'** 是 Mathlib 中的一个引理，位于命名空间 `Ma
troid`。
形式化陈述：isColoop_iff_forall_mem_closure_iff_mem' : M.IsColoop e ↔ (forall X, X sub
seteq M.E -> (e in M.closure X ↔ e in X)) ∧ e in M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isColoop_iff_forall_mem_closure_iff_mem`：isColoop_iff_forall_mem
_closure_iff_mem : M.IsColoop e ↔ (forall X, e in M.closure X ↔ e in X)
· 使用定理 `Matroid.IsColoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M
.IsColoop e → e ∈ M.E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A version of `Matroid.isColoop_iff_forall_mem_closure_iff_mem` where we only qua
ntify
over subsets of the ground set.
-/
lemma isColoop_iff_forall_mem_closure_iff_mem' :
    M.IsColoop e ↔ (∀ X, X ⊆ M.E → (e ∈ M.closure X ↔ e ∈ X)) ∧ e ∈ M.E := by
  refine ⟨fun h ↦ ⟨fun X _ ↦ isColoop_iff_forall_mem_closure_iff_mem.1 h X, h.mem_ground⟩,
    fun ⟨h, he⟩ ↦ isColoop_iff_forall_mem_closure_iff_mem.2 fun X ↦ ?_⟩
  rw [← closure_inter_ground, h _ inter_subset_right, mem_inter_iff, and_iff_left he]
/-
**Matroid.IsColoop.mem_closure_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColo
op`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {X : Set α}, M.IsColoop e → (e ∈ 
M.closure X ↔ e ∈ X)
参数：e ∈ M.closure X ↔ e ∈ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isColoop_iff_forall_mem_closure_iff_mem`：isColoop_iff_forall_mem
_closure_iff_mem : M.IsColoop e ↔ (forall X, e in M.closure X ↔ e in X)
-/
lemma IsColoop.mem_closure_iff_mem (he : M.IsColoop e) : e ∈ M.closure X ↔ e ∈ X :=
  (isColoop_iff_forall_mem_closure_iff_mem.1 he) X
/-
**Matroid.IsColoop.mem_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsColoo
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {X : Set α}, M.IsColoop e → e ∈ M
.closure X → e ∈ X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsColoop.mem_closure_iff_mem`：∀ {α : Type u_1} {M : Matroid α} {
e : α} {X : Set α}, M.IsColoop e → (e ∈ M.closure X ↔ e ∈ X)
-/
lemma IsColoop.mem_of_mem_closure (he : M.IsColoop e) (heX : e ∈ M.closure X) : e ∈ X :=
  he.mem_closure_iff_mem.1 heX
/-
**Matroid.isColoop_iff_sdiff_not_spanning** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isColoop_iff_sdiff_not_spanning : M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Matroid.isColoop_tfae`：isColoop_tfae (M : Matroid α) (e : α) : List.TFAE
 [ M.IsColoop e, e in M.coloops, M.IsCocircuit {e}, forall ⦃B⦄, M.IsBase B -> e 
in B, (fora…
-/
lemma isColoop_iff_sdiff_not_spanning : M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e}) :=
  (M.isColoop_tfae e).out 0 6

@[deprecated (since := "2026-06-03")]
alias isColoop_iff_diff_not_spanning := isColoop_iff_sdiff_not_spanning

alias ⟨IsColoop.sdiff_not_spanning, _⟩ := isColoop_iff_sdiff_not_spanning
/-
**Matroid.isColoop_iff_sdiff_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isColoop_iff_sdiff_closure : M.IsColoop e ↔ M.closure (M.E \ {e}) != M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isColoop_iff_sdiff_not_spanning`：isColoop_iff_sdiff_not_spanning
 : M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e})
· 使用引理 `Matroid.spanning_iff_closure_eq`：spanning_iff_closure_eq (hS : S subsete
q M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isColoop_iff_sdiff_closure : M.IsColoop e ↔ M.closure (M.E \ {e}) ≠ M.E := by
  rw [isColoop_iff_sdiff_not_spanning, spanning_iff_closure_eq]

@[deprecated (since := "2026-06-03")] alias isColoop_iff_diff_closure := isColoop_iff_sdiff_closure
/-
**Matroid.isColoop_iff_notMem_closure_compl** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isColoop_iff_notMem_closure_compl (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isColoop_iff_sdiff_closure`：isColoop_iff_sdiff_closure : M.IsCol
oop e ↔ M.closure (M.E \ {e}) != M.E
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma isColoop_iff_notMem_closure_compl (he : e ∈ M.E := by aesop_mat) :
    M.IsColoop e ↔ e ∉ M.closure (M.E \ {e}) := by
  rw [isColoop_iff_sdiff_closure, not_iff_not]
  refine ⟨fun h ↦ by rwa [h], fun h ↦ (M.closure_subset_ground _).antisymm fun x hx ↦ ?_⟩
  obtain (rfl | hne) := eq_or_ne x e
  · assumption
  exact M.subset_closure (M.E \ {e}) sdiff_subset (show x ∈ M.E \ {e} from ⟨hx, hne⟩)
/-
**Matroid.IsBase.isColoop_iff_forall_notMem_fundCircuit** 是 Mathlib 中的一个定理，位于命名空
间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {B : Set α},   M.IsBase B → e ∈ B
 → (M.IsColoop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCircuit x B)
参数：M.IsColoop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCircuit x B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsColoop.notMem_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {e :
 α} {C : Set α}, M.IsColoop e → M.IsCircuit C → e ∉ C
· 使用定理 `Matroid.IsBase.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {
x : α} {B : Set α}, M.IsBase B → x ∈ M.E → x ∉ B → M.IsCircuit (M.fundCircuit x 
B)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem`：∀ {α : Type u_1} {
M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → e ∈ M.closure (C \ {
e})
· 使用引理 `Matroid.mem_fundCircuit`：mem_fundCircuit (M : Matroid α) (e : α) (I : Se
t α) : e in fundCircuit M e I
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用引理 `Matroid.fundCircuit_subset_insert`：fundCircuit_subset_insert (M : Matroi
d α) (e : α) (I : Set α) : M.fundCircuit e I subseteq insert e I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Matroid.isColoop_iff_notMem_closure_compl`：isColoop_iff_notMem_closure_c
ompl (he : e in M.E
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用定理 `Matroid.Indep.notMem_closure_sdiff_of_mem`：∀ {α : Type u_2} {M : Matroid
 α} {e : α} {I : Set α}, M.Indep I → e ∈ I → e ∉ M.closure (I \ {e})
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
-/
lemma IsBase.isColoop_iff_forall_notMem_fundCircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.IsColoop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCircuit x B := by
  refine ⟨fun h x hx heC ↦ (h.notMem_isCircuit <| hB.fundCircuit_isCircuit hx.1 hx.2) heC,
    fun h ↦ ?_⟩
  have h' : M.E \ {e} ⊆ M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x ≠ e⟩
    obtain (hx | hx) := em (x ∈ B)
    · exact M.subset_closure (B \ {e}) (sdiff_subset.trans hB.subset_ground) ⟨hx, hne⟩
    have h_cct := (hB.fundCircuit_isCircuit hxE hx).mem_closure_sdiff_singleton_of_mem
      (M.mem_fundCircuit x B)
    refine (M.closure_subset_closure (subset_sdiff_singleton ?_ ?_)) h_cct
    · simpa using fundCircuit_subset_insert ..
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [isColoop_iff_notMem_closure_compl (hB.subset_ground he)]
  exact notMem_subset (M.closure_subset_closure_of_subset_closure h') <|
    hB.indep.notMem_closure_sdiff_of_mem he
/-
**Matroid.IsBasis'.inter_coloops_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsBasis' I X → X ∩ M.col
oops ⊆ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsColoop.mem_closure_iff_mem`：∀ {α : Type u_1} {M : Matroid α} {
e : α} {X : Set α}, M.IsColoop e → (e ∈ M.closure X ↔ e ∈ X)
· 使用定理 `Matroid.IsBasis.closure_eq_right`：∀ {α : Type u_2} {M : Matroid α} {X I 
: Set α}, M.IsBasis I (M.closure X) → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis'.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α}
 {X I : Set α}, M.IsBasis' I X → M.IsBasis I (M.closure X)
-/
lemma IsBasis'.inter_coloops_subset (hIX : M.IsBasis' I X) : X ∩ M.coloops ⊆ I := by
  intro e ⟨heX, (heI : M.IsColoop e)⟩
  rwa [← heI.mem_closure_iff_mem, hIX.isBasis_closure_right.closure_eq_right,
    heI.mem_closure_iff_mem]
/-
**Matroid.IsBasis.inter_coloops_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasi
s`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsBasis I X → X ∩ M.colo
ops ⊆ I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.inter_coloops_subset`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → X ∩ M.coloops ⊆ I
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.inter_coloops_subset (hIX : M.IsBasis I X) : X ∩ M.coloops ⊆ I :=
  hIX.isBasis'.inter_coloops_subset
/-
**Matroid.exists_mem_isCircuit_of_not_isColoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroi
d`。
形式化陈述：exists_mem_isCircuit_of_not_isColoop (heE : e in M.E) (he : ¬ M.IsColoop e
) : exists C, M.IsCircuit C ∧ e in C
参数：heE : e in M.E；he : ¬ M.IsColoop e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.IsBase.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {
x : α} {B : Set α}, M.IsBase B → x ∈ M.E → x ∉ B → M.IsCircuit (M.fundCircuit x 
B)
-/
lemma exists_mem_isCircuit_of_not_isColoop (heE : e ∈ M.E) (he : ¬ M.IsColoop e) :
    ∃ C, M.IsCircuit C ∧ e ∈ C := by
  simp only [isColoop_iff_forall_mem_isBase, not_forall, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp]
/-
**Matroid.closure_inter_coloops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_inter_coloops_eq (M : Matroid α) (X : Set α) : M.closure X inter M
.coloops = X inter M.coloops
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsColoop.mem_closure_iff_mem`：∀ {α : Type u_1} {M : Matroid α} {
e : α} {X : Set α}, M.IsColoop e → (e ∈ M.closure X ↔ e ∈ X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma closure_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure X ∩ M.coloops = X ∩ M.coloops := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← isColoop_iff_mem_coloops, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]
/-
**Matroid.closure_inter_eq_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：closure_inter_eq_of_subset_coloops (X : Set α) (hK : K subseteq M.coloops)
 : M.closure X inter K = X inter K
参数：X : Set α；hK : K subseteq M.coloops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用引理 `Matroid.closure_inter_coloops_eq`：closure_inter_coloops_eq (M : Matroid 
α) (X : Set α) : M.closure X inter M.coloops = X inter M.coloops
-/
lemma closure_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
     M.closure X ∩ K = X ∩ K := by
  nth_rw 1 [← inter_eq_self_of_subset_right hK]
  rw [← inter_assoc, closure_inter_coloops_eq, inter_assoc, inter_eq_self_of_subset_right hK]
/-
**Matroid.closure_union_eq_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：closure_union_eq_of_subset_coloops (X : Set α) (hK : K subseteq M.coloops)
 : M.closure (X union K) = M.closure X union K
参数：X : Set α；hK : K subseteq M.coloops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_union_closure_left_eq`：∀ {α : Type u_2} (M : Matroid α) 
(X Y : Set α), M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y)
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `_private.Mathlib.Combinatorics.Matroid.Basic.0.Matroid.subset_ground_of_
subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, X ⊆ Y → Y ⊆ M.E → X ⊆ M.
E
· 使用引理 `Matroid.coloops_subset_ground`：coloops_subset_ground (M : Matroid α) : M
.coloops subseteq M.E
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.mem_closure_iff_exists_isCircuit`：mem_closure_iff_exists_isCircu
it (he : e ∉ X) : e in M.closure X ↔ exists C subseteq insert e X, M.IsCircuit C
 ∧ e in C
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Matroid.IsCircuit.disjoint_coloops`：∀ {α : Type u_1} {M : Matroid α} {C 
: Set α}, M.IsCircuit C → Disjoint C M.coloops
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
· 使用定理 `Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem`：∀ {α : Type u_1} {
M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → e ∈ M.closure (C \ {
e})
-/
lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
    M.closure (X ∪ K) = M.closure X ∪ K := by
  rw [← closure_union_closure_left_eq, subset_antisymm_iff, and_iff_left (M.subset_closure _),
    ← sdiff_eq_empty, eq_empty_iff_forall_notMem]
  refine fun e ⟨hecl, he⟩ ↦ he (.inl ?_)
  obtain ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_exists_isCircuit he).1 hecl
  rw [← singleton_union, ← union_assoc, union_comm, ← sdiff_subset_iff,
    (hC.disjoint_coloops.mono_right hK).sdiff_eq_left, singleton_union] at hCss
  exact M.closure_subset_closure_of_subset_closure (by simpa) <|
    hC.mem_closure_sdiff_singleton_of_mem heC
/-
**Matroid.closure_insert_isColoop_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_insert_isColoop_eq (X : Set α) (he : M.IsColoop e) : M.closure (in
sert e X) = insert e (M.closure X)
参数：X : Set α；he : M.IsColoop e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用引理 `Matroid.closure_union_eq_of_subset_coloops`：closure_union_eq_of_subset_c
oloops (X : Set α) (hK : K subseteq M.coloops) : M.closure (X union K) = M.closu
re X union K
-/
lemma closure_insert_isColoop_eq (X : Set α) (he : M.IsColoop e) :
    M.closure (insert e X) = insert e (M.closure X) := by
  rw [← union_singleton, closure_union_eq_of_subset_coloops _ (by simpa), union_singleton]
/-
**Matroid.closure_eq_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_eq_of_subset_coloops (hK : K subseteq M.coloops) : M.closure K = K
 union M.loops
参数：hK : K subseteq M.coloops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用引理 `Matroid.closure_union_eq_of_subset_coloops`：closure_union_eq_of_subset_c
oloops (X : Set α) (hK : K subseteq M.coloops) : M.closure (X union K) = M.closu
re X union K
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Matroid.closure_empty`：closure_empty (M : Matroid α) : M.closure ∅ = M.l
oops
-/
lemma closure_eq_of_subset_coloops (hK : K ⊆ M.coloops) : M.closure K = K ∪ M.loops := by
  rw [← empty_union K, closure_union_eq_of_subset_coloops _ hK, empty_union, union_comm,
    closure_empty]
/-
**Matroid.closure_sdiff_eq_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：closure_sdiff_eq_of_subset_coloops (X : Set α) (hK : K subseteq M.coloops)
 : M.closure (X \ K) = M.closure X \ K
参数：X : Set α；hK : K subseteq M.coloops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Matroid.closure_union_eq_of_subset_coloops`：closure_union_eq_of_subset_c
oloops (X : Set α) (hK : K subseteq M.coloops) : M.closure (X union K) = M.closu
re X union K
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sdiff_eq_self_iff_disjoint`：sdiff_eq_self_iff_disjoint : x \ y = x ↔ Dis
joint y x
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsColoop.mem_closure_iff_mem`：∀ {α : Type u_1} {M : Matroid α} {
e : α} {X : Set α}, M.IsColoop e → (e ∈ M.closure X ↔ e ∈ X)
-/
lemma closure_sdiff_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
    M.closure (X \ K) = M.closure X \ K := by
  nth_rw 2 [← inter_union_sdiff X K]
  rw [union_comm, closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK),
    union_sdiff_distrib, sdiff_eq_empty.mpr inter_subset_right, union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [IsColoop.mem_closure_iff_mem (hK heK)] at heX
  exact heX.2 heK

@[deprecated (since := "2026-06-03")]
alias closure_diff_eq_of_subset_coloops := closure_sdiff_eq_of_subset_coloops
/-
**Matroid.closure_disjoint_of_disjoint_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名
空间 `Matroid`。
形式化陈述：closure_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : 
K subseteq M.coloops) : Disjoint (M.closure X) K
参数：hXK : Disjoint X K；hK : K subseteq M.coloops。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用引理 `Matroid.closure_inter_eq_of_subset_coloops`：closure_inter_eq_of_subset_c
oloops (X : Set α) (hK : K subseteq M.coloops) : M.closure X inter K = X inter K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma closure_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M.coloops) :
    Disjoint (M.closure X) K := by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]
/-
**Matroid.closure_disjoint_coloops_of_disjoint_coloops** 是 Mathlib 中的一个引理，位于命名空间
 `Matroid`。
形式化陈述：closure_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M.coloops))
 : Disjoint (M.closure X) M.coloops
参数：hX : Disjoint X (M.coloops)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_disjoint_of_disjoint_of_subset_coloops`：closure_disjoint
_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K subseteq M.coloops) 
: Disjoint (M.closure X) K
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma closure_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M.coloops)) :
    Disjoint (M.closure X) M.coloops :=
  closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl
/-
**Matroid.closure_union_coloops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：closure_union_coloops_eq (M : Matroid α) (X : Set α) : M.closure (X union 
M.coloops) = M.closure X union M.coloops
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.closure_union_eq_of_subset_coloops`：closure_union_eq_of_subset_c
oloops (X : Set α) (hK : K subseteq M.coloops) : M.closure (X union K) = M.closu
re X union K
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma closure_union_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.coloops) = M.closure X ∪ M.coloops :=
  closure_union_eq_of_subset_coloops _ Subset.rfl
/-
**Matroid.IsColoop.notMem_closure_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sColoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {X : Set α}, M.IsColoop e → e ∉ X
 → e ∉ M.closure X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsColoop.mem_closure_iff_mem`：∀ {α : Type u_1} {M : Matroid α} {
e : α} {X : Set α}, M.IsColoop e → (e ∈ M.closure X ↔ e ∈ X)
-/
lemma IsColoop.notMem_closure_of_notMem (he : M.IsColoop e) (hX : e ∉ X) : e ∉ M.closure X :=
  mt he.mem_closure_iff_mem.mp hX
/-
**Matroid.IsColoop.insert_indep_of_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCo
loop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {I : Set α}, M.IsColoop e → M.Ind
ep I → M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.notMem_closure_iff_of_notMem`：∀ {α : Type u_2} {M : Matroi
d α} {e : α} {I : Set α},   M.Indep I →     e ∉ I →       autoParam (e ∈ M.E) Ma
troid.Indep.notMem_closure_iff_o…
· 使用定理 `Matroid.IsColoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M
.IsColoop e → e ∈ M.E
· 使用定理 `Matroid.IsColoop.notMem_closure_of_notMem`：∀ {α : Type u_1} {M : Matroid
 α} {e : α} {X : Set α}, M.IsColoop e → e ∉ X → e ∉ M.closure X
-/
lemma IsColoop.insert_indep_of_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := by
  refine (em (e ∈ I)).elim (fun h ↦ by rwa [insert_eq_of_mem h]) fun h ↦ ?_
  rw [← hI.notMem_closure_iff_of_notMem h]
  exact he.notMem_closure_of_notMem h
/-
**Matroid.union_indep_iff_indep_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Mat
roid`。
形式化陈述：union_indep_iff_indep_of_subset_coloops (hK : K subseteq M.coloops) : M.In
dep (I union K) ↔ M.Indep I
参数：hK : K subseteq M.coloops。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsColoop.mem_of_isBase`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {B : Set α}, M.IsColoop e → M.IsBase B → e ∈ B
-/
lemma union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M.coloops) :
    M.Indep (I ∪ K) ↔ M.Indep I := by
  refine ⟨fun h ↦ h.subset subset_union_left, fun h ↦ ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ IsColoop.mem_of_isBase he hB))
/-
**Matroid.sdiff_indep_iff_indep_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Mat
roid`。
形式化陈述：sdiff_indep_iff_indep_of_subset_coloops (hK : K subseteq M.coloops) : M.In
dep (I \ K) ↔ M.Indep I
参数：hK : K subseteq M.coloops。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.union_indep_iff_indep_of_subset_coloops`：union_indep_iff_indep_o
f_subset_coloops (hK : K subseteq M.coloops) : M.Indep (I union K) ↔ M.Indep I
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sdiff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M.coloops) :
    M.Indep (I \ K) ↔ M.Indep I := by
  rw [← union_indep_iff_indep_of_subset_coloops hK, sdiff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]

@[deprecated (since := "2026-06-03")]
alias diff_indep_iff_indep_of_subset_coloops := sdiff_indep_iff_indep_of_subset_coloops

@[simp]
/-
**Matroid.union_coloops_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：union_coloops_indep_iff : M.Indep (I union M.coloops) ↔ M.Indep I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.union_indep_iff_indep_of_subset_coloops`：union_indep_iff_indep_o
f_subset_coloops (hK : K subseteq M.coloops) : M.Indep (I union K) ↔ M.Indep I
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma union_coloops_indep_iff : M.Indep (I ∪ M.coloops) ↔ M.Indep I :=
  union_indep_iff_indep_of_subset_coloops Subset.rfl

@[simp]
/-
**Matroid.sdiff_coloops_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：sdiff_coloops_indep_iff : M.Indep (I \ M.coloops) ↔ M.Indep I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.sdiff_indep_iff_indep_of_subset_coloops`：sdiff_indep_iff_indep_o
f_subset_coloops (hK : K subseteq M.coloops) : M.Indep (I \ K) ↔ M.Indep I
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma sdiff_coloops_indep_iff : M.Indep (I \ M.coloops) ↔ M.Indep I :=
  sdiff_indep_iff_indep_of_subset_coloops Subset.rfl

@[deprecated (since := "2026-06-03")] alias diff_coloops_indep_iff := sdiff_coloops_indep_iff
/-
**Matroid.coloops_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：coloops_indep (M : Matroid α) : M.Indep M.coloops
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用引理 `Matroid.union_coloops_indep_iff`：union_coloops_indep_iff : M.Indep (I un
ion M.coloops) ↔ M.Indep I
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
-/
lemma coloops_indep (M : Matroid α) : M.Indep M.coloops := by
  rw [← empty_union M.coloops, union_coloops_indep_iff]
  exact M.empty_indep
/-
**Matroid.restrict_isColoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_isColoop_iff {R : Set α} (hRE : R subseteq M.E) : (M ↾ R).IsColoo
p e ↔ e ∉ M.closure (R \ {e}) ∧ e in R
参数：hRE : R subseteq M.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isColoop_iff_forall_notMem_isCircuit`：isColoop_iff_forall_notMem
_isCircuit (he : e in M.E
· 使用引理 `Matroid.mem_closure_iff_exists_isCircuit`：mem_closure_iff_exists_isCircu
it (he : e ∉ X) : e in M.closure X ↔ exists C subseteq insert e X, M.IsCircuit C
 ∧ e in C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Matroid.restrict_isCircuit_iff`：restrict_isCircuit_iff (hR : R subseteq 
M.E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.IsColoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M
.IsColoop e → e ∈ M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma restrict_isColoop_iff {R : Set α} (hRE : R ⊆ M.E) :
    (M ↾ R).IsColoop e ↔ e ∉ M.closure (R \ {e}) ∧ e ∈ R := by
  wlog heR : e ∈ R
  · exact iff_of_false (fun h ↦ heR h.mem_ground) fun h ↦ heR h.2
  rw [isColoop_iff_forall_notMem_isCircuit heR, mem_closure_iff_exists_isCircuit (by simp)]
  simp only [restrict_isCircuit_iff hRE, insert_sdiff_singleton]
  aesop

/-- If two matroids agree on loops and coloops, and have the same independent sets after
  loops/coloops are removed, they are equal. -/
/-
**Matroid.ext_indep_disjoint_loops_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_indep_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
l : M₁.loops = M₂.loops) (hc : M₁.coloops = M₂.coloops) (h : forall I, I subsete
q M₁.E -> Disjoint I (M₁.loops union M₁.coloops) -> (M₁.Indep I ↔ M₂.Indep I)) :
 M₁ = M₂
参数：hE : M₁.E = M₂.E；hl : M₁.loops = M₂.loops；hc : M₁.coloops = M₂.coloops；h : fo
rall I, I subseteq M₁.E -> Disjoint I (M₁.loops union M₁.coloops) -> (M₁.Indep I
 ↔ M₂.Indep I)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.sdiff_coloops_indep_iff`：sdiff_coloops_indep_iff : M.Indep (I \ 
M.coloops) ↔ M.Indep I
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `Set.disjoint_union_right`：disjoint_union_right : Disjoint s (t union u) 
↔ Disjoint s t ∧ Disjoint s u
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.IsLoop.not_indep_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α
} {X : Set α}, M.IsLoop e → e ∈ X → ¬M.Indep X
· 使用定理 `Matroid.IsLoop.not_isColoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M
.IsLoop e → ¬M.IsColoop e
· 使用引理 `Matroid.isLoop_iff`：isLoop_iff : M.IsLoop e ↔ e in M.loops

--- 原说明 ---
If two matroids agree on loops and coloops, and have the same independent sets a
fter
  loops/coloops are removed, they are equal.
-/
lemma ext_indep_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.loops = M₂.loops) (hc : M₁.coloops = M₂.coloops)
    (h : ∀ I, I ⊆ M₁.E → Disjoint I (M₁.loops ∪ M₁.coloops) → (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine ext_indep hE fun I hI ↦ ?_
  rw [← sdiff_coloops_indep_iff, ← @sdiff_coloops_indep_iff _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.loops))
  · rw [h _ (sdiff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left sdiff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩) ?_
  rw [isLoop_iff, hl, ← isLoop_iff] at hel
  rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩

end IsColoop

section Loopless

/-- A Matroid is `Loopless` if it has no loop -/
@[mk_iff]
/-
**Matroid.Loopless** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Matroid is `Loopless` if it has no loop
-/
class Loopless (M : Matroid α) : Prop where
  loops_eq_empty : M.loops = ∅

@[simp]
/-
**Matroid.loops_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：loops_eq_empty (M : Matroid α) [Loopless M] : M.loops = ∅
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Loopless.loops_eq_empty`：∀ {α : Type u_1} {M : Matroid α} [self 
: M.Loopless], M.loops = ∅
-/
lemma loops_eq_empty (M : Matroid α) [Loopless M] : M.loops = ∅ :=
  ‹Loopless M›.loops_eq_empty
/-
**Matroid.isNonloop_of_loopless** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_of_loopless [Loopless M] (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.not_isLoop_iff`：not_isLoop_iff (he : e in M.E
· 使用引理 `Matroid.isLoop_iff`：isLoop_iff : M.IsLoop e ↔ e in M.loops
· 使用引理 `Matroid.loops_eq_empty`：loops_eq_empty (M : Matroid α) [Loopless M] : M.
loops = ∅
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
lemma isNonloop_of_loopless [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff, isLoop_iff, loops_eq_empty]
  exact notMem_empty _
/-
**Matroid.subsingleton_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：subsingleton_indep [M.Loopless] (hI : I.Subsingleton) (hIE : I subseteq M.
E
参数：hI : I.Subsingleton。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.isNonloop_of_loopless`：isNonloop_of_loopless [Loopless M] (he : 
e in M.E
-/
lemma subsingleton_indep [M.Loopless] (hI : I.Subsingleton) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  obtain rfl | ⟨x, rfl⟩ := hI.eq_empty_or_singleton
  · simp
  simpa using M.isNonloop_of_loopless
/-
**Matroid.not_isLoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：not_isLoop (M : Matroid α) [Loopless M] (e : α) : ¬ M.IsLoop e
参数：M : Matroid α；e : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
· 使用引理 `Matroid.isNonloop_of_loopless`：isNonloop_of_loopless [Loopless M] (he : 
e in M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma not_isLoop (M : Matroid α) [Loopless M] (e : α) : ¬ M.IsLoop e :=
  fun h ↦ (isNonloop_of_loopless (e := e)).not_isLoop h
/-
**Matroid.loopless_iff_forall_isNonloop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：loopless_iff_forall_isNonloop : M.Loopless ↔ forall e in M.E, M.IsNonloop 
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.isNonloop_of_loopless`：isNonloop_of_loopless [Loopless M] (he : 
e in M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
· 使用定理 `Matroid.IsLoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.I
sLoop e → e ∈ M.E
-/
lemma loopless_iff_forall_isNonloop : M.Loopless ↔ ∀ e ∈ M.E, M.IsNonloop e :=
  ⟨fun _ _ he ↦ isNonloop_of_loopless he,
    fun h ↦ ⟨subset_empty_iff.1 (fun e (he : M.IsLoop e) ↦ (h e he.mem_ground).not_isLoop he)⟩⟩
/-
**Matroid.loopless_iff_forall_not_isLoop** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：loopless_iff_forall_not_isLoop : M.Loopless ↔ forall e in M.E, ¬ M.IsLoop 
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.not_isLoop`：not_isLoop (M : Matroid α) [Loopless M] (e : α) : ¬ 
M.IsLoop e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.loopless_iff_forall_isNonloop`：loopless_iff_forall_isNonloop : M
.Loopless ↔ forall e in M.E, M.IsNonloop e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.not_isLoop_iff`：not_isLoop_iff (he : e in M.E
-/
lemma loopless_iff_forall_not_isLoop : M.Loopless ↔ ∀ e ∈ M.E, ¬ M.IsLoop e :=
  ⟨fun _ e _ ↦ M.not_isLoop e,
    fun h ↦ loopless_iff_forall_isNonloop.2 fun e he ↦ (not_isLoop_iff he).1 (h e he)⟩
/-
**Matroid.loopless_iff_forall_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：loopless_iff_forall_isCircuit : M.Loopless ↔ forall C, M.IsCircuit C -> C.
Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsLoop.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.Is
Loop e → M.IsCircuit {e}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `Matroid.IsCircuit.nonempty`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}
, M.IsCircuit C → C.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsLoop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.I
sLoop e → e ∈ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.singleton_isCircuit`：singleton_isCircuit : M.IsCircuit {e} ↔ M.I
sLoop e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.loopless_iff_forall_not_isLoop`：loopless_iff_forall_not_isLoop :
 M.Loopless ↔ forall e in M.E, ¬ M.IsLoop e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma loopless_iff_forall_isCircuit : M.Loopless ↔ ∀ C, M.IsCircuit C → C.Nontrivial := by
  suffices (∃ x ∈ M.E, M.IsLoop x) ↔ ∃ x, M.IsCircuit x ∧ x.Subsingleton by
    rw [loopless_iff_forall_not_isLoop]
    contrapose!
    exact this
  refine ⟨fun ⟨e, _, he⟩ ↦ ⟨{e}, he.isCircuit, by simp⟩, fun ⟨C, hC, hCs⟩ ↦ ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_isCircuit.1 hC).mem_ground, singleton_isCircuit.1 hC⟩
/-
**Matroid.Loopless.ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Loopless`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) [M.Loopless], M.E = {e | M.IsNonloop e}
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Matroid.isNonloop_of_loopless`：isNonloop_of_loopless [Loopless M] (he : 
e in M.E
· 使用定理 `Matroid.IsNonloop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → e ∈ M.E
-/
lemma Loopless.ground_eq (M : Matroid α) [Loopless M] : M.E = {e | M.IsNonloop e} :=
  Set.ext fun _ ↦ ⟨fun he ↦ isNonloop_of_loopless he, IsNonloop.mem_ground⟩
/-
**Matroid.IsRestriction.loopless** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestrictio
n`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} [M.Loopless], N.IsRestriction M → N.Loo
pless
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.loopless_iff`：∀ {α : Type u_1} (M : Matroid α), M.Loopless ↔ M.l
oops = ∅
· 使用引理 `Matroid.restrict_loops_eq`：restrict_loops_eq {R : Set α} (hR : R subsete
q M.E) : (M ↾ R).loops = M.loops inter R
· 使用引理 `Matroid.loops_eq_empty`：loops_eq_empty (M : Matroid α) [Loopless M] : M.
loops = ∅
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsRestriction.loopless [M.Loopless] (hR : N ≤r M) : N.Loopless := by
  obtain ⟨R, hR, rfl⟩ := hR
  rw [loopless_iff, restrict_loops_eq hR, M.loops_eq_empty, empty_inter]
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Matroid α} [M.Nonempty] [Loopless M] : RankPos M :=
  M.ground_nonempty.elim fun _ he ↦ (isNonloop_of_loopless he).rankPos
/-
**Matroid.loopyOn_isLoopless_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E : Set α}, (Matroid.loopyOn E).Loopless ↔ E = ∅
参数：Matroid.loopyOn E。
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
@[simp] lemma loopyOn_isLoopless_iff {E : Set α} : Loopless (loopyOn E) ↔ E = ∅ := by
  simp [loopless_iff_forall_not_isLoop, eq_empty_iff_forall_notMem]

/-- The loopless matroid obtained from `M` by deleting all its loops. -/
/-
**Matroid.removeLoops** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：removeLoops (M : Matroid α) : Matroid α
参数：M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The loopless matroid obtained from `M` by deleting all its loops.
-/
def removeLoops (M : Matroid α) : Matroid α := M ↾ {e | M.IsNonloop e}
/-
**Matroid.removeLoops_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_eq_restrict (M : Matroid α) : M.removeLoops = M ↾ {e | M.IsNon
loop e}
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma removeLoops_eq_restrict (M : Matroid α) : M.removeLoops = M ↾ {e | M.IsNonloop e} := rfl
/-
**Matroid.removeLoops_ground_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.IsNonloop
 e}
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.IsNonloop e} := rfl
/-
**Matroid.removeLoops_loopless** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：removeLoops_loopless (M : Matroid α) : Loopless M.removeLoops
参数：M : Matroid α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance removeLoops_loopless (M : Matroid α) : Loopless M.removeLoops := by
  simp [loopless_iff_forall_isNonloop, removeLoops]

@[simp]
/-
**Matroid.removeLoops_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.removeLoops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.removeLoop
s = M.restrict {e | M.IsNonloop e}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Loopless.ground_eq`：∀ {α : Type u_1} (M : Matroid α) [M.Loopless
], M.E = {e | M.IsNonloop e}
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
-/
lemma removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M := by
  rw [removeLoops, ← Loopless.ground_eq, restrict_ground_eq_self]
/-
**Matroid.removeLoops_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_eq_self_iff : M.removeLoops = M ↔ M.Loopless
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.removeLoops_eq_self`：removeLoops_eq_self (M : Matroid α) [Loople
ss M] : M.removeLoops = M
-/
lemma removeLoops_eq_self_iff : M.removeLoops = M ↔ M.Loopless := by
  refine ⟨fun h ↦ ?_, fun h ↦ M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance
/-
**Matroid.removeLoops_isRestriction** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_isRestriction (M : Matroid α) : M.removeLoops <=r M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.restrict_isRestriction`：restrict_isRestriction (M : Matroid α) (
R : Set α) (hR : R subseteq M.E
· 使用定理 `Matroid.IsNonloop.mem_ground`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → e ∈ M.E
-/
lemma removeLoops_isRestriction (M : Matroid α) : M.removeLoops ≤r M :=
  restrict_isRestriction _ _ (fun _ h ↦ IsNonloop.mem_ground h)
/-
**Matroid.eq_restrict_removeLoops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eq_restrict_removeLoops (M : Matroid α) : M.removeLoops ↾ M.E = M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.removeLoops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.removeLoop
s = M.restrict {e | M.IsNonloop e}
· 使用定理 `Matroid.ext_iff_indep`：ext_iff_indep {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ (M₁
.E = M₂.E) ∧ forall ⦃I⦄, I subseteq M₁.E -> (M₁.Indep I ↔ M₂.Indep I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.Indep.isNonloop_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → e ∈ I → M.IsNonloop e
-/
lemma eq_restrict_removeLoops (M : Matroid α) : M.removeLoops ↾ M.E = M := by
  rw [removeLoops, ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE ↦ ⟨ fun hI ↦ hI.1.1, fun hI ↦ ⟨⟨hI,fun e heI ↦ hI.isNonloop_of_mem heI⟩, hIE⟩⟩

@[simp]
/-
**Matroid.removeLoops_indep_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_indep_eq : M.removeLoops.Indep = M.Indep
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.removeLoops_eq_restrict`：removeLoops_eq_restrict (M : Matroid α)
 : M.removeLoops = M ↾ {e | M.IsNonloop e}
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `Matroid.Indep.isNonloop_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → e ∈ I → M.IsNonloop e
-/
lemma removeLoops_indep_eq : M.removeLoops.Indep = M.Indep := by
  ext I
  rw [removeLoops_eq_restrict, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun h e ↦ h.isNonloop_of_mem

@[simp]
/-
**Matroid.removeLoops_isBasis'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, M.removeLoops.IsBasis' = M.IsBasis'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Matroid.removeLoops_indep_eq`：removeLoops_indep_eq : M.removeLoops.Indep
 = M.Indep
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma removeLoops_isBasis'_eq : M.removeLoops.IsBasis' = M.IsBasis' := by
  ext
  simp [IsBasis']
/-
**Matroid.removeLoops_isBase_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, M.removeLoops.IsBase = M.IsBase
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_iff_maximal_indep`：isBase_iff_maximal_indep : M.IsBase B 
↔ Maximal M.Indep B
· 使用引理 `Matroid.removeLoops_indep_eq`：removeLoops_indep_eq : M.removeLoops.Indep
 = M.Indep
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma removeLoops_isBase_eq : M.removeLoops.IsBase = M.IsBase := by
  ext B
  rw [isBase_iff_maximal_indep, removeLoops_indep_eq, isBase_iff_maximal_indep]

@[simp]
/-
**Matroid.removeLoops_isNonloop_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_isNonloop_eq : M.removeLoops.IsNonloop = M.IsNonloop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.removeLoops_eq_restrict`：removeLoops_eq_restrict (M : Matroid α)
 : M.removeLoops = M ↾ {e | M.IsNonloop e}
· 使用引理 `Matroid.restrict_isNonloop_iff`：restrict_isNonloop_iff {R : Set α} : (M 
↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e in R
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma removeLoops_isNonloop_eq : M.removeLoops.IsNonloop = M.IsNonloop := by
  ext e
  rw [removeLoops_eq_restrict, restrict_isNonloop_iff, mem_ofPred, and_self]
/-
**Matroid.IsNonloop.removeLoops_isNonloop** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsN
onloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsNonloop e → M.removeLoops.Is
Nonloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Matroid.removeLoops_isNonloop_eq`：removeLoops_isNonloop_eq : M.removeLoo
ps.IsNonloop = M.IsNonloop
-/
lemma IsNonloop.removeLoops_isNonloop (he : M.IsNonloop e) : M.removeLoops.IsNonloop e := by
  simpa
/-
**Matroid.removeLoops_idem** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_idem (M : Matroid α) : M.removeLoops.removeLoops = M.removeLoo
ps
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.removeLoops_eq_self`：removeLoops_eq_self (M : Matroid α) [Loople
ss M] : M.removeLoops = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma removeLoops_idem (M : Matroid α) : M.removeLoops.removeLoops = M.removeLoops := by
  simp
/-
**Matroid.removeLoops_restrict_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_restrict_eq_restrict (hX : X subseteq {e | M.IsNonloop e}) : M
.removeLoops ↾ X = M ↾ X
参数：hX : X subseteq {e | M.IsNonloop e}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.removeLoops_eq_restrict`：removeLoops_eq_restrict (M : Matroid α)
 : M.removeLoops = M ↾ {e | M.IsNonloop e}
· 使用定理 `Matroid.restrict_restrict_eq`：restrict_restrict_eq {R₁ R₂ : Set α} (M : 
Matroid α) (hR : R₂ subseteq R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂
-/
lemma removeLoops_restrict_eq_restrict (hX : X ⊆ {e | M.IsNonloop e}) :
    M.removeLoops ↾ X = M ↾ X := by
  rwa [removeLoops_eq_restrict, restrict_restrict_eq]

@[simp]
/-
**Matroid.restrict_univ_removeLoops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_univ_removeLoops_eq : (M ↾ univ).removeLoops = M.removeLoops
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.removeLoops_eq_restrict`：removeLoops_eq_restrict (M : Matroid α)
 : M.removeLoops = M ↾ {e | M.IsNonloop e}
· 使用定理 `Matroid.restrict_restrict_eq`：restrict_restrict_eq {R₁ R₂ : Set α} (M : 
Matroid α) (hR : R₂ subseteq R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_univ_removeLoops_eq : (M ↾ univ).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_restrict, restrict_restrict_eq _ (subset_univ _), removeLoops_eq_restrict]
  simp
/-
**Matroid.IsRestriction.isRestriction_removeLoops** 是 Mathlib 中的一个定理，位于命名空间 `Mat
roid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → ∀ [N.Loopless], N.
IsRestriction M.removeLoops
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.exists_eq_restrict`：∀ {α : Type u_1} {M N : Matroi
d α}, N.IsRestriction M → ∃ R ⊆ M.E, N = M.restrict R
· 使用定理 `Matroid.IsRestriction.of_subset`：∀ {α : Type u_1} {R R' : Set α} (M : Ma
troid α), R ⊆ R' → (M.restrict R).IsRestriction (M.restrict R')
· 使用定理 `Matroid.IsNonloop.of_restrict`：∀ {α : Type u_1} {M : Matroid α} {e : α} 
{R : Set α}, (M.restrict R).IsNonloop e → M.IsNonloop e
· 使用引理 `Matroid.isNonloop_of_loopless`：isNonloop_of_loopless [Loopless M] (he : 
e in M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsRestriction.isRestriction_removeLoops (hNM : N ≤r M) [N.Loopless] : N ≤r M.removeLoops := by
  obtain ⟨R, hR, rfl⟩ := hNM.exists_eq_restrict
  exact IsRestriction.of_subset M fun e heR ↦ ((M ↾ R).isNonloop_of_loopless heR).of_restrict
/-
**Matroid.removeLoops_mono_isRestriction** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：removeLoops_mono_isRestriction (hNM : N <=r M) : N.removeLoops <=r M.remov
eLoops
参数：hNM : N <=r M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.isRestriction_removeLoops`：∀ {α : Type u_1} {M N :
 Matroid α}, N.IsRestriction M → ∀ [N.Loopless], N.IsRestriction M.removeLoops
· 使用定理 `Matroid.IsRestriction.trans`：∀ {α : Type u_1} {M₁ M₂ M₃ : Matroid α}, M₁
.IsRestriction M₂ → M₂.IsRestriction M₃ → M₁.IsRestriction M₃
· 使用引理 `Matroid.removeLoops_isRestriction`：removeLoops_isRestriction (M : Matroi
d α) : M.removeLoops <=r M
-/
lemma removeLoops_mono_isRestriction (hNM : N ≤r M) : N.removeLoops ≤r M.removeLoops :=
  ((removeLoops_isRestriction _).trans hNM).isRestriction_removeLoops

end Loopless

end Matroid

