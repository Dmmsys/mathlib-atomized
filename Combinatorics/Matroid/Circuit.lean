/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Closure

/-!
# Matroid IsCircuits

A 'Circuit' of a matroid `M` is a minimal set `C` that is dependent in `M`.
A matroid is determined by its set of circuits, and often the circuits
offer a more compact description of a matroid than the collection of independent sets or bases.
In matroids arising from graphs, circuits correspond to graphical cycles.

## Main Declarations

* `Matroid.IsCircuit M C` means that `C` is minimally dependent in `M`.
* For an `Indep`endent set `I` whose closure contains an element `e ∉ I`,
  `Matroid.fundCircuit M e I` is the unique circuit contained in `insert e I`.
* `Matroid.Indep.fundCircuit_isCircuit` states that `Matroid.fundCircuit M e I` is indeed a circuit.
* `Matroid.IsCircuit.eq_fundCircuit_of_subset` states that `Matroid.fundCircuit M e I` is the
  unique circuit contained in `insert e I`.
* `Matroid.dep_iff_superset_isCircuit` states that the dependent subsets of the ground set
  are precisely those that contain a circuit.
* `Matroid.ext_isCircuit` : a matroid is determined by its collection of circuits.
* `Matroid.IsCircuit.strong_multi_elimination` : the strong circuit elimination rule for an
  infinite collection of circuits.
* `Matroid.IsCircuit.strong_elimination` : the strong circuit elimination rule for two circuits.
* `Matroid.finitary_iff_forall_isCircuit_finite` : finitary matroids are precisely those whose
  circuits are all finite.
* `Matroid.IsCocircuit M C` means that `C` is minimally dependent in `M✶`,
  or equivalently that `M.E \ C` is a hyperplane of `M`.
* `Matroid.fundCocircuit M B e` is the unique cocircuit that intersects the base `B` precisely
  in the element `e`.
* `Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit` : `e` is in the fundamental circuit
  for `B` and `f` iff `f` is in the fundamental cocircuit for `B` and `e`.

## Implementation Details

Since `Matroid.fundCircuit M e I` is only sensible if `I` is independent and `e ∈ M.closure I \ I`,
to avoid hypotheses being explicitly included in the definition,
junk values need to be chosen if either hypothesis fails.
The definition is chosen so that the junk values satisfy
`M.fundCircuit e I = {e}` for `e ∈ I` or `e ∉ M.E` and
`M.fundCircuit e I = insert e I` if `e ∈ M.E \ M.closure I`.
These make the useful statement `e ∈ M.fundCircuit e I ⊆ insert e I` true unconditionally.
-/

@[expose] public section

variable {α : Type*} {M : Matroid α} {C C' I X Y R : Set α} {e f x y : α}

open Set

namespace Matroid

/-- `M.IsCircuit C` means that `C` is a minimal dependent set in `M`. -/
/-
**Matroid.IsCircuit** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsCircuit (M : Matroid α)
参数：M : Matroid α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.IsCircuit C` means that `C` is a minimal dependent set in `M`.
-/
def IsCircuit (M : Matroid α) := Minimal M.Dep
/-
**Matroid.isCircuit_def** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCircuit_def : M.IsCircuit C ↔ Minimal M.Dep C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCircuit_def : M.IsCircuit C ↔ Minimal M.Dep C := Iff.rfl
/-
**Matroid.IsCircuit.dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → M.Dep C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
-/
lemma IsCircuit.dep (hC : M.IsCircuit C) : M.Dep C :=
  hC.prop
/-
**Matroid.IsCircuit.not_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → ¬M.Indep C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
  hC.dep.not_indep
/-
**Matroid.IsCircuit.minimal** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → Minimal M.De
p C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCircuit.minimal (hC : M.IsCircuit C) : Minimal M.Dep C :=
  hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
/-
**Matroid.IsCircuit.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → C ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma IsCircuit.subset_ground (hC : M.IsCircuit C) : C ⊆ M.E :=
  hC.dep.subset_ground
/-
**Matroid.IsCircuit.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → C.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.nonempty`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.De
p D → D.Nonempty
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma IsCircuit.nonempty (hC : M.IsCircuit C) : C.Nonempty :=
  hC.dep.nonempty
/-
**Matroid.empty_not_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：empty_not_isCircuit (M : Matroid α) : ¬M.IsCircuit ∅
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.nonempty`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}
, M.IsCircuit C → C.Nonempty
-/
lemma empty_not_isCircuit (M : Matroid α) : ¬M.IsCircuit ∅ :=
  fun h ↦ by simpa using h.nonempty
/-
**Matroid.isCircuit_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCircuit_iff : M.IsCircuit C ↔ M.Dep C ∧ forall ⦃D⦄, M.Dep D -> D subsete
q C -> D = C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCircuit_iff : M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃D⦄, M.Dep D → D ⊆ C → D = C := by
  simp_rw [isCircuit_def, minimal_subset_iff, eq_comm (a := C)]
/-
**Matroid.IsCircuit.ssubset_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C X : Set α}, M.IsCircuit C → X ⊂ C → M.
Indep X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, autoP
aram (X ⊆ M.E) Matroid.not_dep_iff._auto_1 → (¬M.Dep X ↔ M.Indep X)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isCircuit_iff`：isCircuit_iff : M.IsCircuit C ↔ M.Dep C ∧ forall 
⦃D⦄, M.Dep D -> D subseteq C -> D = C
-/
lemma IsCircuit.ssubset_indep (hC : M.IsCircuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h ↦ hXC.ne ((isCircuit_iff.1 hC).2 h hXC.subset)
/-
**Matroid.IsCircuit.minimal_not_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircu
it`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → Minimal (fun
 x => ¬M.Indep x) C
参数：fun x => ¬M.Indep x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.IsCircuit.not_indep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α
}, M.IsCircuit C → ¬M.Indep C
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matroid.IsCircuit.ssubset_indep`：∀ {α : Type u_1} {M : Matroid α} {C X :
 Set α}, M.IsCircuit C → X ⊂ C → M.Indep X
-/
lemma IsCircuit.minimal_not_indep (hC : M.IsCircuit C) : Minimal (¬ M.Indep ·) C := by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a ↦ ssubset_indep hC a
/-
**Matroid.isCircuit_iff_minimal_not_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCircuit_iff_minimal_not_indep (hCE : C subseteq M.E) : M.IsCircuit C ↔ M
inimal (¬ M.Indep ·) C
参数：hCE : C subseteq M.E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.minimal_not_indep`：∀ {α : Type u_1} {M : Matroid α} {C
 : Set α}, M.IsCircuit C → Minimal (fun x => ¬M.Indep x) C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Minimal.eq_of_superset`：Minimal.eq_of_superset (h : Minimal P s) (ht : P
 t) (hts : t subseteq s) : s = t
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
-/
lemma isCircuit_iff_minimal_not_indep (hCE : C ⊆ M.E) : M.IsCircuit C ↔ Minimal (¬ M.Indep ·) C :=
  ⟨IsCircuit.minimal_not_indep, fun h ↦ ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC ↦ (h.eq_of_superset hJ.not_indep hJC).le⟩⟩
/-
**Matroid.IsCircuit.sdiff_singleton_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsC
ircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ 
C → M.Indep (C \ {e})
参数：C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.ssubset_indep`：∀ {α : Type u_1} {M : Matroid α} {C X :
 Set α}, M.IsCircuit C → X ⊂ C → M.Indep X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.sdiff_singleton_ssubset`：sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a i
n s
-/
lemma IsCircuit.sdiff_singleton_indep (hC : M.IsCircuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (sdiff_singleton_ssubset.2 he)

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_indep := IsCircuit.sdiff_singleton_indep
/-
**Matroid.isCircuit_iff_forall_ssubset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCircuit_iff_forall_ssubset : M.IsCircuit C ↔ M.Dep C ∧ forall ⦃I⦄, I ⊂ C
 -> M.Indep I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsCircuit.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.IsCircuit = 
Minimal M.Dep
· 使用定理 `Set.minimal_iff_forall_ssubset`：Set.minimal_iff_forall_ssubset : Minimal
 P s ↔ P s ∧ forall ⦃t⦄, t ⊂ s -> ¬ P t
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.not_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, autoP
aram (X ⊆ M.E) Matroid.not_dep_iff._auto_1 → (¬M.Dep X ↔ M.Indep X)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
-/
lemma isCircuit_iff_forall_ssubset : M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  rw [IsCircuit, minimal_iff_forall_ssubset, and_congr_right_iff]
  exact fun h ↦ ⟨fun h' I hIC ↦ ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC ↦ (h hIC).not_dep⟩
/-
**Matroid.isCircuit_antichain** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCircuit_antichain : IsAntichain (· subseteq ·) (Set.ofPred M.IsCircuit)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Minimal.eq_of_subset`：Minimal.eq_of_subset (h : Minimal P s) (ht : P t) 
(hts : t subseteq s) : t = s
· 使用定理 `Matroid.IsCircuit.minimal`：∀ {α : Type u_1} {M : Matroid α} {C : Set α},
 M.IsCircuit C → Minimal M.Dep C
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma isCircuit_antichain : IsAntichain (· ⊆ ·) (Set.ofPred M.IsCircuit) :=
  fun _ hC _ hC' hne hss ↦ hne <| (IsCircuit.minimal hC').eq_of_subset hC.dep hss
/-
**Matroid.IsCircuit.eq_of_not_indep_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Circuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C X : Set α}, M.IsCircuit C → ¬M.Indep X
 → X ⊆ C → X = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Matroid.IsCircuit.ssubset_indep`：∀ {α : Type u_1} {M : Matroid α} {C X :
 Set α}, M.IsCircuit C → X ⊂ C → M.Indep X
-/
lemma IsCircuit.eq_of_not_indep_subset (hC : M.IsCircuit C) (hX : ¬ M.Indep X) (hXC : X ⊆ C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)
/-
**Matroid.IsCircuit.eq_of_dep_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircui
t`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C X : Set α}, M.IsCircuit C → M.Dep X → 
X ⊆ C → X = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.eq_of_not_indep_subset`：∀ {α : Type u_1} {M : Matroid 
α} {C X : Set α}, M.IsCircuit C → ¬M.Indep X → X ⊆ C → X = C
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
-/
lemma IsCircuit.eq_of_dep_subset (hC : M.IsCircuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC
/-
**Matroid.IsCircuit.not_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C C' : Set α}, M.IsCircuit C → M.IsCircu
it C' → ¬C' ⊂ C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsCircuit.eq_of_dep_subset`：∀ {α : Type u_1} {M : Matroid α} {C 
X : Set α}, M.IsCircuit C → M.Dep X → X ⊆ C → X = C
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
-/
lemma IsCircuit.not_ssubset (hC : M.IsCircuit C) (hC' : M.IsCircuit C') : ¬C' ⊂ C :=
  fun h' ↦ h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)
/-
**Matroid.IsCircuit.eq_of_subset_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Circuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C C' : Set α}, M.IsCircuit C → M.IsCircu
it C' → C ⊆ C' → C = C'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.eq_of_dep_subset`：∀ {α : Type u_1} {M : Matroid α} {C 
X : Set α}, M.IsCircuit C → M.Dep X → X ⊆ C → X = C
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma IsCircuit.eq_of_subset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C ⊆ C') :
    C = C' :=
  hC'.eq_of_dep_subset hC.dep h
/-
**Matroid.IsCircuit.eq_of_superset_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C C' : Set α}, M.IsCircuit C → M.IsCircu
it C' → C' ⊆ C → C = C'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsCircuit.eq_of_subset_isCircuit`：∀ {α : Type u_1} {M : Matroid 
α} {C C' : Set α}, M.IsCircuit C → M.IsCircuit C' → C ⊆ C' → C = C'
-/
lemma IsCircuit.eq_of_superset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C' ⊆ C) :
    C = C' :=
  (hC'.eq_of_subset_isCircuit hC h).symm
/-
**Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep** 是 Mathlib 中的一个引理，位于命名
空间 `Matroid`。
形式化陈述：isCircuit_iff_dep_forall_sdiff_singleton_indep : M.IsCircuit C ↔ M.Dep C ∧
 forall e in C, M.Indep (C \ {e})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCircuit_iff_minimal_not_indep`：isCircuit_iff_minimal_not_indep
 (hCE : C subseteq M.E) : M.IsCircuit C ↔ Minimal (¬ M.Indep ·) C
· 使用定理 `Set.minimal_iff_forall_sdiff_singleton`：Set.minimal_iff_forall_sdiff_sin
gleton (hP : forall ⦃s t⦄, P t -> t subseteq s -> P s) : Minimal P s ↔ P s ∧ for
all x in s, ¬ P (s \ {x})
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isCircuit_iff_dep_forall_sdiff_singleton_indep :
    M.IsCircuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  wlog hCE : C ⊆ M.E
  · exact iff_of_false (hCE ∘ IsCircuit.subset_ground) (fun h ↦ hCE h.1.subset_ground)
  simp [isCircuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_sdiff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX ↦ hY <| hX.subset hYX)]

@[deprecated (since := "2026-06-03")]
alias isCircuit_iff_dep_forall_diff_singleton_indep :=
  isCircuit_iff_dep_forall_sdiff_singleton_indep

/-! ### Independence and bases -/

/-
**Matroid.Indep.insert_isCircuit_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.In
dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {e : α},   M.Indep I → e ∉ I 
→ e ∈ M.closure I → (∀ f ∈ I, e ∉ M.closure (I \ {f})) → M.IsCircuit (insert e I
)
参数：∀ f ∈ I, e ∉ M.closure (I \ {f})；insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep`：isCircuit_iff_de
p_forall_sdiff_singleton_indep : M.IsCircuit C ↔ M.Dep C ∧ forall e in C, M.Inde
p (C \ {e})
· 使用定理 `Matroid.Indep.insert_dep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α} {
I : Set α}, M.Indep I → (M.Dep (insert e I) ↔ e ∈ M.closure I \ I)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton_comm`：insert_sdiff_singleton_comm (hab : a !=
 b) (s : Set α) : insert a (s \ {b}) = insert a s \ {b}
· 使用定理 `Matroid.Indep.insert_indep_iff_of_notMem`：∀ {α : Type u_2} {M : Matroid 
α} {e : α} {I : Set α}, M.Indep I → e ∉ I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.
closure I)
· 使用定理 `Matroid.Indep.sdiff`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Ind
ep I → ∀ (X : Set α), M.Indep (I \ X)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用引理 `Matroid.mem_ground_of_mem_closure`：mem_ground_of_mem_closure (he : e in 
M.closure X) : e in M.E

--- 原说明 ---
### Independence and bases
-/
lemma Indep.insert_isCircuit_of_forall (hI : M.Indep I) (heI : e ∉ I) (he : e ∈ M.closure I)
    (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep, hI.insert_dep_iff, and_iff_right ⟨he, heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_sdiff_singleton_comm (by rintro rfl; contradiction),
    (hI.sdiff _).insert_indep_iff_of_notMem (by simp [heI])]
  exact ⟨mem_ground_of_mem_closure he, h f hfI⟩
/-
**Matroid.Indep.insert_isCircuit_of_forall_of_nontrivial** 是 Mathlib 中的一个定理，位于命名
空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {e : α},   M.Indep I → I.Nont
rivial → e ∈ M.closure I → (∀ f ∈ I, e ∉ M.closure (I \ {f})) → M.IsCircuit (ins
ert e I)
参数：∀ f ∈ I, e ∉ M.closure (I \ {f})；insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.insert_isCircuit_of_forall`：∀ {α : Type u_1} {M : Matroid 
α} {I : Set α} {e : α},   M.Indep I → e ∉ I → e ∈ M.closure I → (∀ f ∈ I, e ∉ M.
closure (I \ {f})) → M.IsCircu…
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Indep.insert_isCircuit_of_forall_of_nontrivial (hI : M.Indep I) (hInt : I.Nontrivial)
    (he : e ∈ M.closure I) (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  refine hI.insert_isCircuit_of_forall (fun heI ↦ ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))
/-
**Matroid.IsCircuit.sdiff_singleton_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ 
C → M.IsBasis (C \ {e}) C
参数：C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Matroid.Indep.isBasis_insert_iff`：∀ {α : Type u_1} {M : Matroid α} {I : 
Set α} {e : α},   M.Indep I → (M.IsBasis I (insert e I) ↔ M.Dep (insert e I) ∨ e
 ∈ I)
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_indep`：∀ {α : Type u_1} {M : Matroid α
} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.Indep (C \ {e})
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma IsCircuit.sdiff_singleton_isBasis (hC : M.IsCircuit C) (he : e ∈ C) :
    M.IsBasis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_sdiff_singleton, (hC.sdiff_singleton_indep he).isBasis_insert_iff,
    insert_sdiff_singleton, insert_eq_of_mem he]
  exact Or.inl hC.dep

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_isBasis := IsCircuit.sdiff_singleton_isBasis
/-
**Matroid.IsCircuit.isBasis_iff_eq_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C I : Set α}, M.IsCircuit C → (M.IsBasis
 I C ↔ ∃ e ∈ C, I = C \ {e})
参数：M.IsBasis I C ↔ ∃ e ∈ C, I = C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_indep`：∀ {α : Type u_1} {M : Matroid α
} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.Indep (C \ {e})
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_isBasis`：∀ {α : Type u_1} {M : Matroid
 α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.IsBasis (C \ {e}) C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsCircuit.isBasis_iff_eq_sdiff_singleton (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ ∃ e ∈ C, I = C \ {e} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.sdiff_singleton_indep he.1)
      (subset_sdiff_singleton h.subset he.2) sdiff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.sdiff_singleton_isBasis he

@[deprecated (since := "2026-06-03")]
alias IsCircuit.isBasis_iff_eq_diff_singleton := IsCircuit.isBasis_iff_eq_sdiff_singleton
/-
**Matroid.IsCircuit.isBasis_iff_insert_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsC
ircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C I : Set α}, M.IsCircuit C → (M.IsBasis
 I C ↔ ∃ e ∈ C \ I, C = insert e I)
参数：M.IsBasis I C ↔ ∃ e ∈ C \ I, C = insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsCircuit.isBasis_iff_eq_sdiff_singleton`：∀ {α : Type u_1} {M : 
Matroid α} {C I : Set α}, M.IsCircuit C → (M.IsBasis I C ↔ ∃ e ∈ C, I = C \ {e})
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
-/
lemma IsCircuit.isBasis_iff_insert_eq (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ ∃ e ∈ C \ I, C = insert e I := by
  rw [hC.isBasis_iff_eq_sdiff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ ↦ ⟨e, ⟨he, fun heI ↦ (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ ↦ ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_sdiff_singleton, insert_eq_of_mem he]
  rw [hC, insert_sdiff_self_of_notMem he.2]

/-! ### Restriction -/

/-
**Matroid.IsCircuit.isCircuit_restrict_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C R : Set α}, M.IsCircuit C → C ⊆ R → (M
.restrict R).IsCircuit C
参数：M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
### Restriction
-/
lemma IsCircuit.isCircuit_restrict_of_subset (hC : M.IsCircuit C) (hCR : C ⊆ R) :
    (M ↾ R).IsCircuit C := by
  simp_rw [isCircuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩
/-
**Matroid.restrict_isCircuit_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_isCircuit_iff (hR : R subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsCircuit.isCircuit_restrict_of_subset`：∀ {α : Type u_1} {M : Ma
troid α} {C R : Set α}, M.IsCircuit C → C ⊆ R → (M.restrict R).IsCircuit C
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma restrict_isCircuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).IsCircuit C ↔ M.IsCircuit C ∧ C ⊆ R := by
  refine ⟨?_, fun h ↦ h.1.isCircuit_restrict_of_subset h.2⟩
  simp_rw [isCircuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

/-! ### Fundamental IsCircuits -/

/-- For an independent set `I` and some `e ∈ M.closure I \ I`,
`M.fundCircuit e I` is the unique circuit contained in `insert e I`.
For the fact that this is a circuit, see `Matroid.Indep.fundCircuit_isCircuit`,
and the fact that it is unique, see `Matroid.IsCircuit.eq_fundCircuit_of_subset`.
Has the junk value `{e}` if `e ∈ I` or `e ∉ M.E`, and `insert e I` if `e ∈ M.E \ M.closure I`. -/
/-
**Matroid.fundCircuit** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：fundCircuit (M : Matroid α) (e : α) (I : Set α) : Set α
参数：M : Matroid α；e : α；I : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an independent set `I` and some `e ∈ M.closure I \ I`,
`M.fundCircuit e I` is the unique circuit contained in `insert e I`.
For the fact that this is a circuit, see `Matroid.Indep.fundCircuit_isCircuit`,
and the fact that it is unique, see `Matroid.IsCircuit.eq_fundCircuit_of_subset`
.
Has the junk value `{e}` if `e ∈ I` or `e ∉ M.E`, and `insert e I` if `e ∈ M.E \
 M.closure I`.
-/
def fundCircuit (M : Matroid α) (e : α) (I : Set α) : Set α :=
  insert e (I ∩ ⋂₀ {J | J ⊆ I ∧ M.closure {e} ⊆ M.closure J})
/-
**Matroid.fundCircuit_eq_sInter** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_eq_sInter (he : e in M.closure I) : M.fundCircuit e I = insert
 e (⋂₀ {J | J subseteq I ∧ e in M.closure J})
参数：he : e in M.closure I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.fundCircuit.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α) (I : 
Set α),   M.fundCircuit e I = insert e (I ∩ ⋂₀ {J | J ⊆ I ∧ M.closure {e} ⊆ M.cl
osure J})
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Matroid.closure_subset_closure_iff_subset_closure`：closure_subset_closur
e_iff_subset_closure (hX : X subseteq M.E
· 使用引理 `Matroid.mem_ground_of_mem_closure`：mem_ground_of_mem_closure (he : e in 
M.closure X) : e in M.E
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma fundCircuit_eq_sInter (he : e ∈ M.closure I) :
    M.fundCircuit e I = insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}) := by
  rw [fundCircuit]
  simp_rw [closure_subset_closure_iff_subset_closure
    (show {e} ⊆ M.E by simpa using mem_ground_of_mem_closure he), singleton_subset_iff]
  rw [inter_eq_self_of_subset_right (sInter_subset_of_mem (by simpa))]
/-
**Matroid.fundCircuit_subset_insert** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_subset_insert (M : Matroid α) (e : α) (I : Set α) : M.fundCirc
uit e I subseteq insert e I
参数：M : Matroid α；e : α；I : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma fundCircuit_subset_insert (M : Matroid α) (e : α) (I : Set α) :
    M.fundCircuit e I ⊆ insert e I :=
  insert_subset_insert inter_subset_left
/-
**Matroid.fundCircuit_subset_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_subset_ground (he : e in M.E) (hI : I subseteq M.E
参数：he : e in M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.fundCircuit_subset_insert`：fundCircuit_subset_insert (M : Matroi
d α) (e : α) (I : Set α) : M.fundCircuit e I subseteq insert e I
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
-/
lemma fundCircuit_subset_ground (he : e ∈ M.E) (hI : I ⊆ M.E := by aesop_mat) :
    M.fundCircuit e I ⊆ M.E :=
  (M.fundCircuit_subset_insert e I).trans (insert_subset he hI)
/-
**Matroid.mem_fundCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_fundCircuit (M : Matroid α) (e : α) (I : Set α) : e in fundCircuit M e
 I
参数：M : Matroid α；e : α；I : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
lemma mem_fundCircuit (M : Matroid α) (e : α) (I : Set α) : e ∈ fundCircuit M e I :=
  mem_insert ..
/-
**Matroid.fundCircuit_sdiff_eq_inter** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_sdiff_eq_inter (M : Matroid α) (heI : e ∉ I) : (M.fundCircuit 
e I) \ {e} = (M.fundCircuit e I) inter I
参数：M : Matroid α；heI : e ∉ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma fundCircuit_sdiff_eq_inter (M : Matroid α) (heI : e ∉ I) :
    (M.fundCircuit e I) \ {e} = (M.fundCircuit e I) ∩ I :=
  (subset_inter sdiff_subset (by simp [fundCircuit_subset_insert])).antisymm
    (subset_sdiff_singleton inter_subset_left (by simp [heI]))

@[deprecated (since := "2026-06-03")] alias fundCircuit_diff_eq_inter := fundCircuit_sdiff_eq_inter

/-- The fundamental isCircuit of `e` and `X` has the junk value `{e}` if `e ∈ X` -/
/-
**Matroid.fundCircuit_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_eq_of_mem (heX : e in X) : M.fundCircuit e X = {e}
参数：heX : e in X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
The fundamental isCircuit of `e` and `X` has the junk value `{e}` if `e ∈ X`
-/
lemma fundCircuit_eq_of_mem (heX : e ∈ X) : M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ t ⊆ X, M.closure {e} ⊆ M.closure t → a ∈ t) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun b hbX h ↦ h _ (singleton_subset_iff.2 heX) Subset.rfl
/-
**Matroid.fundCircuit_eq_of_notMem_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_eq_of_notMem_ground (heX : e ∉ M.E) : M.fundCircuit e X = {e}
参数：heX : e ∉ M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_inter_eq_empty`：singleton_inter_eq_empty : {a} inter s = ∅
 ↔ a ∉ s
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma fundCircuit_eq_of_notMem_ground (heX : e ∉ M.E) : M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ t ⊆ X, M.closure {e} ⊆ M.closure t → a ∈ t) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  simp_rw [← M.closure_inter_ground {e}, singleton_inter_eq_empty.2 heX]
  exact fun a haX h ↦ by simpa using h ∅ (empty_subset X) rfl.subset
/-
**Matroid.Indep.fundCircuit_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {e : α},   M.Indep I → e ∈ M.
closure I → e ∉ I → M.IsCircuit (M.fundCircuit e I)
参数：M.fundCircuit e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Matroid.fundCircuit_eq_sInter`：fundCircuit_eq_sInter (he : e in M.closur
e I) : M.fundCircuit e I = insert e (⋂₀ {J | J subseteq I ∧ e in M.closure J})
· 使用定理 `Matroid.Indep.insert_isCircuit_of_forall`：∀ {α : Type u_1} {M : Matroid 
α} {I : Set α} {e : α},   M.Indep I → e ∉ I → e ∈ M.closure I → (∀ f ∈ I, e ∉ M.
closure (I \ {f})) → M.IsCircu…
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matroid.Indep.closure_sInter_eq_biInter_closure_of_forall_subset`：∀ {α :
 Type u_2} {M : Matroid α} {I : Set α} {Js : Set (Set α)},   M.Indep I → Js.None
mpty → (∀ J ∈ Js, J ⊆ I) → M.closure (⋂₀ Js) = ⋂ J ∈ J…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma Indep.fundCircuit_isCircuit (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    M.IsCircuit (M.fundCircuit e I) := by
  have aux : ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J} ⊆ I := sInter_subset_of_mem (by simpa)
  rw [fundCircuit_eq_sInter hecl]
  refine (hI.subset aux).insert_isCircuit_of_forall ?_ ?_ ?_
  · simp [show ∃ x ⊆ I, e ∈ M.closure x ∧ e ∉ x from ⟨I, by simp [hecl, heI]⟩]
  · rw [hI.closure_sInter_eq_biInter_closure_of_forall_subset ⟨I, by simpa⟩ (by simp +contextual)]
    simp
  simp only [mem_sInter, mem_ofPred_eq, and_imp]
  exact fun f hf hecl ↦ (hf _ (sdiff_subset.trans aux) hecl).2 rfl
/-
**Matroid.Indep.mem_fundCircuit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {e x : α},   M.Indep I → e ∈ 
M.closure I → e ∉ I → (x ∈ M.fundCircuit e I ↔ M.Indep (insert e I \ {x}))
参数：x ∈ M.fundCircuit e I ↔ M.Indep (insert e I \ {x})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matroid.Indep.sdiff`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Ind
ep I → ∀ (X : Set α), M.Indep (I \ X)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.fundCircuit_eq_sInter`：fundCircuit_eq_sInter (he : e in M.closur
e I) : M.fundCircuit e I = insert e (⋂₀ {J | J subseteq I ∧ e in M.closure J})
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.insert_sdiff_singleton_comm`：insert_sdiff_singleton_comm (hab : a !=
 b) (s : Set α) : insert a (s \ {b}) = insert a s \ {b}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Matroid.Indep.insert_indep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → (M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I)
· 使用引理 `Matroid.mem_ground_of_mem_closure`：mem_ground_of_mem_closure (he : e in 
M.closure X) : e in M.E
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma Indep.mem_fundCircuit_iff (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    x ∈ M.fundCircuit e I ↔ M.Indep (insert e I \ {x}) := by
  obtain rfl | hne := eq_or_ne x e
  · simp [hI.sdiff, mem_fundCircuit]
  suffices (∀ t ⊆ I, e ∈ M.closure t → x ∈ t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCircuit_eq_sInter hecl, hne, ← insert_sdiff_singleton_comm hne.symm,
      (hI.sdiff _).insert_indep_iff, mem_ground_of_mem_closure hecl, heI]
  refine ⟨fun h hecl ↦ (h _ sdiff_subset hecl).2 rfl, fun h J hJ heJ ↦ by_contra fun hxJ ↦ h ?_⟩
  exact M.closure_subset_closure (subset_sdiff_singleton hJ hxJ) heJ
/-
**Matroid.IsBase.fundCircuit_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {x : α} {B : Set α}, M.IsBase B → x ∈ M.E
 → x ∉ B → M.IsCircuit (M.fundCircuit x B)
参数：M.fundCircuit x B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {I
 : Set α} {e : α},   M.Indep I → e ∈ M.closure I → e ∉ I → M.IsCircuit (M.fundCi
rcuit e I)
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
-/
lemma IsBase.fundCircuit_isCircuit {B : Set α} (hB : M.IsBase B) (hxE : x ∈ M.E) (hxB : x ∉ B) :
    M.IsCircuit (M.fundCircuit x B) :=
  hB.indep.fundCircuit_isCircuit (by rwa [hB.closure_eq]) hxB

/-- For `I` independent, `M.fundCircuit e I` is the only circuit contained in `insert e I`. -/
/-
**Matroid.IsCircuit.eq_fundCircuit_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C I : Set α} {e : α},   M.IsCircuit C → 
M.Indep I → C ⊆ insert e I → C = M.fundCircuit e I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.subset_insert_iff`：subset_insert_iff : s subseteq insert a t ↔ s sub
seteq t ∨ (a in s ∧ s \ {a} subseteq t)
· 使用定理 `Matroid.IsCircuit.not_indep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α
}, M.IsCircuit C → ¬M.Indep C
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_isBasis`：∀ {α : Type u_1} {M : Matroid
 α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.IsBasis (C \ {e}) C
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.fundCircuit_eq_sInter`：fundCircuit_eq_sInter (he : e in M.closur
e I) : M.fundCircuit e I = insert e (⋂₀ {J | J subseteq I ∧ e in M.closure J})
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.IsCircuit.eq_of_superset_isCircuit`：∀ {α : Type u_1} {M : Matroi
d α} {C C' : Set α}, M.IsCircuit C → M.IsCircuit C' → C' ⊆ C → C = C'
· 使用定理 `Matroid.Indep.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {I
 : Set α} {e : α},   M.Indep I → e ∈ M.closure I → e ∉ I → M.IsCircuit (M.fundCi
rcuit e I)
· 使用定理 `Matroid.Indep.mem_closure_iff`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α} {x : α}, M.Indep I → (x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I)
· 使用定理 `Matroid.Dep.superset`：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   
M.Dep D → D ⊆ X → autoParam (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s

--- 原说明 ---
For `I` independent, `M.fundCircuit e I` is the only circuit contained in `inser
t e I`.
-/
lemma IsCircuit.eq_fundCircuit_of_subset (hC : M.IsCircuit C) (hI : M.Indep I)
    (hCs : C ⊆ insert e I) : C = M.fundCircuit e I := by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I ⊆ C by
    refine hC.eq_of_superset_isCircuit (hI.fundCircuit_isCircuit ?_ fun heI ↦ ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.superset hCs (insert_subset (hC.subset_ground heC) hI.subset_ground))
    exact hC.not_indep (hI.subset (hCs.trans (by simp [heI])))
  have heCcl := (hC.sdiff_singleton_isBasis heC).subset_closure heC
  have heI : e ∈ M.closure I := M.closure_subset_closure hCeI heCcl
  rw [fundCircuit_eq_sInter heI]
  refine insert_subset heC <| (sInter_subset_of_mem (t := C \ {e}) ?_).trans sdiff_subset
  exact ⟨hCeI, heCcl⟩
/-
**Matroid.fundCircuit_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCircuit_restrict {R : Set α} (hIR : I subseteq R) (heR : e in R) (hR :
 R subseteq M.E) : (M ↾ R).fundCircuit e I = M.fundCircuit e I
参数：hIR : I subseteq R；heR : e in R；hR : R subseteq M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Matroid.restrict_closure_eq`：restrict_closure_eq (M : Matroid α) (hXR : 
X subseteq R) (hR : R subseteq M.E
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.sInter_subset_sInter`：sInter_subset_sInter {S T : Set (Set α)} (h : 
S subseteq T) : ⋂₀ T subseteq ⋂₀ S
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma fundCircuit_restrict {R : Set α} (hIR : I ⊆ R) (heR : e ∈ R) (hR : R ⊆ M.E) :
    (M ↾ R).fundCircuit e I = M.fundCircuit e I := by
  simp_rw [fundCircuit, M.restrict_closure_eq (R := R) (X := {e}) (by simpa)]
  apply subset_antisymm
  · gcongr 5 with J hJI; intro heJ
    simp only [restrict_closure_eq']
    refine (inter_subset_inter_left _ ?_).trans subset_union_left
    rwa [inter_eq_self_of_subset_left (hJI.trans hIR)]
  gcongr 5 with J hJI; intro heJ
  refine closure_subset_closure_of_subset_closure ?_
  rw [restrict_closure_eq _ (hJI.trans hIR) hR] at heJ
  simp only [subset_inter_iff, inter_subset_right, and_true] at heJ
  exact subset_trans (by simpa [M.mem_closure_of_mem' (mem_singleton e) (hR heR)]) heJ
/-
**Matroid.fundCircuit_restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {I : Set α} {e : α} (M : Matroid α), (M.restrict Set.univ
).fundCircuit e I = M.fundCircuit e I
参数：M : Matroid α；M.restrict Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.sdiff_inter_self`：sdiff_inter_self {a b : Set α} : b \ a inter a = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma fundCircuit_restrict_univ (M : Matroid α) :
    (M ↾ univ).fundCircuit e I = M.fundCircuit e I := by
  have aux (A B) : M.closure A ⊆ B ∪ univ \ M.E ↔ M.closure A ⊆ B := by
    refine ⟨fun h ↦ ?_, fun h ↦ h.trans subset_union_left⟩
    refine (subset_inter h (M.closure_subset_ground A)).trans ?_
    simp [union_inter_distrib_right]
  simp [fundCircuit, aux]

/-! ### Dependence -/

/-
**Matroid.Dep.exists_isCircuit_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Dep X → ∃ C ⊆ X, M.IsCircu
it C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.fundCircuit_subset_insert`：fundCircuit_subset_insert (M : Matroi
d α) (e : α) (I : Set α) : M.fundCircuit e I subseteq insert e I
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Matroid.Indep.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {I
 : Set α} {e : α},   M.Indep I → e ∈ M.closure I → e ∉ I → M.IsCircuit (M.fundCi
rcuit e I)
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I

--- 原说明 ---
### Dependence
-/
lemma Dep.exists_isCircuit_subset (hX : M.Dep X) : ∃ C, C ⊆ X ∧ M.IsCircuit C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCircuit e I, (M.fundCircuit_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCircuit_isCircuit (hI.subset_closure heX) heI⟩
/-
**Matroid.dep_iff_superset_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dep_iff_superset_isCircuit (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.exists_isCircuit_subset`：∀ {α : Type u_1} {M : Matroid α} {X
 : Set α}, M.Dep X → ∃ C ⊆ X, M.IsCircuit C
· 使用定理 `Matroid.Dep.superset`：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   
M.Dep D → D ⊆ X → autoParam (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
-/
lemma dep_iff_superset_isCircuit (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X ↔ ∃ C, C ⊆ X ∧ M.IsCircuit C :=
  ⟨Dep.exists_isCircuit_subset, fun ⟨C, hCX, hC⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.dep_iff_superset_isCircuit` that has the ground-set hypothesis
as part of the equivalence, rather than a hypothesis. -/
/-
**Matroid.dep_iff_superset_isCircuit'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dep_iff_superset_isCircuit' : M.Dep X ↔ (exists C, C subseteq X ∧ M.IsCirc
uit C) ∧ X subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.exists_isCircuit_subset`：∀ {α : Type u_1} {M : Matroid α} {X
 : Set α}, M.Dep X → ∃ C ⊆ X, M.IsCircuit C
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `Matroid.Dep.superset`：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   
M.Dep D → D ⊆ X → autoParam (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C

--- 原说明 ---
A version of `Matroid.dep_iff_superset_isCircuit` that has the ground-set hypoth
esis
as part of the equivalence, rather than a hypothesis.
-/
lemma dep_iff_superset_isCircuit' : M.Dep X ↔ (∃ C, C ⊆ X ∧ M.IsCircuit C) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.exists_isCircuit_subset, h.subset_ground⟩,
    fun ⟨⟨C, hCX, hC⟩, h⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.indep_iff_forall_subset_not_isCircuit` that has the ground-set
hypothesis as part of the equivalence, rather than a hypothesis. -/
/-
**Matroid.indep_iff_forall_subset_not_isCircuit'** 是 Mathlib 中的一个引理，位于命名空间 `Matr
oid`。
形式化陈述：indep_iff_forall_subset_not_isCircuit' : M.Indep I ↔ (forall C, C subseteq
 I -> ¬M.IsCircuit C) ∧ I subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A version of `Matroid.indep_iff_forall_subset_not_isCircuit` that has the ground
-set
hypothesis as part of the equivalence, rather than a hypothesis.
-/
lemma indep_iff_forall_subset_not_isCircuit' :
    M.Indep I ↔ (∀ C, C ⊆ I → ¬M.IsCircuit C) ∧ I ⊆ M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_isCircuit']
  aesop
/-
**Matroid.indep_iff_forall_subset_not_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matro
id`。
形式化陈述：indep_iff_forall_subset_not_isCircuit (hI : I subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.indep_iff_forall_subset_not_isCircuit'`：indep_iff_forall_subset_
not_isCircuit' : M.Indep I ↔ (forall C, C subseteq I -> ¬M.IsCircuit C) ∧ I subs
eteq M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma indep_iff_forall_subset_not_isCircuit (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ C, C ⊆ I → ¬M.IsCircuit C := by
  rw [indep_iff_forall_subset_not_isCircuit', and_iff_left hI]

/-! ### Closure -/

/-
**Matroid.IsCircuit.closure_sdiff_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), M
.closure (C \ {e}) = M.closure C
参数：e : α；C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_isBasis`：∀ {α : Type u_1} {M : Matroid
 α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.IsBasis (C \ {e}) C
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s

--- 原说明 ---
### Closure
-/
lemma IsCircuit.closure_sdiff_singleton_eq (hC : M.IsCircuit C) (e : α) :
    M.closure (C \ {e}) = M.closure C :=
  (em (e ∈ C)).elim
    (fun he ↦ by rw [(hC.sdiff_singleton_isBasis he).closure_eq_closure])
    (fun he ↦ by rw [sdiff_singleton_eq_self he])

@[deprecated (since := "2026-06-03")]
alias IsCircuit.closure_diff_singleton_eq := IsCircuit.closure_sdiff_singleton_eq
/-
**Matroid.IsCircuit.subset_closure_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), C
 ⊆ M.closure (C \ {e})
参数：e : α；C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsCircuit.closure_sdiff_singleton_eq`：∀ {α : Type u_1} {M : Matr
oid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), M.closure (C \ {e}) = M.closure C
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
-/
lemma IsCircuit.subset_closure_sdiff_singleton (hC : M.IsCircuit C) (e : α) :
    C ⊆ M.closure (C \ {e}) := by
  rw [hC.closure_sdiff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

@[deprecated (since := "2026-06-03")]
alias IsCircuit.subset_closure_diff_singleton := IsCircuit.subset_closure_sdiff_singleton
/-
**Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ 
C → e ∈ M.closure (C \ {e})
参数：C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.subset_closure_sdiff_singleton`：∀ {α : Type u_1} {M : 
Matroid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), C ⊆ M.closure (C \ {e})
-/
lemma IsCircuit.mem_closure_sdiff_singleton_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) :
    e ∈ M.closure (C \ {e}) :=
  hC.subset_closure_sdiff_singleton e heC

@[deprecated (since := "2026-06-03")]
alias IsCircuit.mem_closure_diff_singleton_of_mem := IsCircuit.mem_closure_sdiff_singleton_of_mem
/-
**Matroid.exists_isCircuit_of_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：exists_isCircuit_of_mem_closure (he : e in M.closure X) (heX : e ∉ X) : ex
ists C subseteq insert e X, M.IsCircuit C ∧ e in C
参数：he : e in M.closure X；heX : e ∉ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.fundCircuit_subset_insert`：fundCircuit_subset_insert (M : Matroi
d α) (e : α) (I : Set α) : M.fundCircuit e I subseteq insert e I
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Matroid.Indep.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {I
 : Set α} {e : α},   M.Indep I → e ∈ M.closure I → e ∉ I → M.IsCircuit (M.fundCi
rcuit e I)
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用引理 `Matroid.mem_fundCircuit`：mem_fundCircuit (M : Matroid α) (e : α) (I : Se
t α) : e in fundCircuit M e I
-/
lemma exists_isCircuit_of_mem_closure (he : e ∈ M.closure X) (heX : e ∉ X) :
    ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  let ⟨I, hI⟩ := M.exists_isBasis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_isCircuit (by rwa [hI.closure_eq_closure]) (notMem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩
/-
**Matroid.mem_closure_iff_exists_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_closure_iff_exists_isCircuit (he : e ∉ X) : e in M.closure X ↔ exists 
C subseteq insert e X, M.IsCircuit C ∧ e in C
参数：he : e ∉ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.exists_isCircuit_of_mem_closure`：exists_isCircuit_of_mem_closure
 (he : e in M.closure X) (heX : e ∉ X) : exists C subseteq insert e X, M.IsCircu
it C ∧ e in C
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem`：∀ {α : Type u_1} {
M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → e ∈ M.closure (C \ {
e})
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
-/
lemma mem_closure_iff_exists_isCircuit (he : e ∉ X) :
    e ∈ M.closure X ↔ ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  ⟨fun h ↦ exists_isCircuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ ↦ mem_of_mem_of_subset
    (hC.mem_closure_sdiff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

/-! ### Extensionality -/

/-
**Matroid.ext_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h : forall ⦃C⦄, C su
bseteq M₁.E -> (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ = M₂
参数：hE : M₁.E = M₂.E；h : forall ⦃C⦄, C subseteq M₁.E -> (M₁.IsCircuit C ↔ M₂.IsCi
rcuit C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.indep_iff_forall_subset_not_isCircuit`：indep_iff_forall_subset_n
ot_isCircuit (hI : I subseteq M.E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Extensionality
-/
lemma ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃C⦄, C ⊆ M₁.E → (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ = M₂ := by
  have h' {C} : M₁.IsCircuit C ↔ M₂.IsCircuit C :=
    (em (C ⊆ M₁.E)).elim (h (C := C)) (fun hC ↦ iff_of_false (mt IsCircuit.subset_ground hC)
      (mt IsCircuit.subset_ground fun hss ↦ hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI ↦ ?_
  simp_rw [indep_iff_forall_subset_not_isCircuit hI, h',
    indep_iff_forall_subset_not_isCircuit (hI.trans_eq hE)]

/-- A stronger version of `Matroid.ext_isCircuit`:
two matroids on the same ground set are equal if no circuit of one is independent in the other. -/
/-
**Matroid.ext_isCircuit_not_indep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_isCircuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h₁ : foral
l C, M₁.IsCircuit C -> ¬ M₂.Indep C) (h₂ : forall C, M₂.IsCircuit C -> ¬ M₁.Inde
p C) : M₁ = M₂
参数：hE : M₁.E = M₂.E；h₁ : forall C, M₁.IsCircuit C -> ¬ M₂.Indep C；h₂ : forall C,
 M₂.IsCircuit C -> ¬ M₁.Indep C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.ext_isCircuit`：ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂
.E) (h : forall ⦃C⦄, C subseteq M₁.E -> (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ 
= M₂
· 使用定理 `Matroid.Dep.exists_isCircuit_subset`：∀ {α : Type u_1} {M : Matroid α} {X
 : Set α}, M.Dep X → ∃ C ⊆ X, M.IsCircuit C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsCircuit.eq_of_not_indep_subset`：∀ {α : Type u_1} {M : Matroid 
α} {C X : Set α}, M.IsCircuit C → ¬M.Indep X → X ⊆ C → X = C

--- 原说明 ---
A stronger version of `Matroid.ext_isCircuit`:
two matroids on the same ground set are equal if no circuit of one is independen
t in the other.
-/
lemma ext_isCircuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h₁ : ∀ C, M₁.IsCircuit C → ¬ M₂.Indep C) (h₂ : ∀ C, M₂.IsCircuit C → ¬ M₁.Indep C) :
    M₁ = M₂ := by
  refine ext_isCircuit hE fun C hCE ↦ ⟨fun hC ↦ ?_, fun hC ↦ ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_isCircuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_isCircuit_subset
  rwa [← hC.eq_of_not_indep_subset (h₁ C' hC') hC'C]
/-
**Matroid.ext_iff_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：ext_iff_isCircuit {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ M₁.E = M₂.E ∧ forall C, 
M₁.IsCircuit C ↔ M₂.IsCircuit C
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Matroid.ext_isCircuit`：ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂
.E) (h : forall ⦃C⦄, C subseteq M₁.E -> (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ 
= M₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma ext_iff_isCircuit {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ C, M₁.IsCircuit C ↔ M₂.IsCircuit C :=
  ⟨fun h ↦ by simp [h], fun h ↦ ext_isCircuit h.1 fun C hC ↦ h.2 (C := C)⟩

section Elimination

/-! ### Circuit Elimination -/

variable {ι : Type*} {J C₀ C₁ C₂ : Set α}

/-- A version of `Matroid.IsCircuit.strong_multi_elimination` that is phrased using insertion. -/
/-
**Matroid.IsCircuit.strong_multi_elimination_insert** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {ι : Type u_2} {J : Set α} (x : ι → α) (I
 : ι → Set α) (z : α),   (∀ (i : ι), x i ∉ I i) →     (∀ (i : ι), M.IsCircuit (i
nsert (x i) (I i))) →       M.IsCircuit (J ∪ Set.range x) → z ∈ J → (∀ (i : ι), 
z ∉ I i) → ∃ C' ⊆ J ∪ ⋃ i, I i, M.IsCircuit C' ∧ z ∈ C'
参数：x : ι → α；I : ι → Set α；z : α；∀ (i : ι), x i ∉ I i；∀ (i : ι), M.IsCircuit (in
sert (x i) (I i))；J ∪ Set.range x；∀ (i : ι), z ∉ I i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Matroid.IsCircuit.closure_sdiff_singleton_eq`：∀ {α : Type u_1} {M : Matr
oid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), M.closure (C \ {e}) = M.closure C
· 使用引理 `Matroid.closure_union_congr_left`：closure_union_congr_left {X' : Set α} 
(h : M.closure X = M.closure X') : M.closure (X union Y) = M.closure (X' union Y
)
· 使用引理 `Matroid.closure_iUnion_congr`：closure_iUnion_congr (Xs Ys : ι -> Set α) 
(h : forall i, M.closure (Xs i) = M.closure (Ys i)) : M.closure (⋃ i, Xs i) = M.
closure (⋃ i, Ys i…
· 使用定理 `Set.iUnion_insert_eq_range_union_iUnion`：iUnion_insert_eq_range_union_iU
nion {ι : Type*} (x : ι -> β) (t : ι -> Set β) : ⋃ i, insert (x i) (t i) = range
 x union ⋃ i, t i
· 使用定理 `Set.union_right_comm`：union_right_comm (s₁ s₂ s₃ : Set α) : s₁ union s₂ 
union s₃ = s₁ union s₃ union s₂
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem`：∀ {α : Type u_1} {
M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → e ∈ M.closure (C \ {
e})
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.union_subset_union_left`：union_subset_union_left {s₁ s₂ : Set α} (t)
 (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用引理 `Matroid.mem_closure_iff_exists_isCircuit`：mem_closure_iff_exists_isCircu
it (he : e ∉ X) : e in M.closure X ↔ exists C subseteq insert e X, M.IsCircuit C
 ∧ e in C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `Matroid.IsCircuit.strong_multi_elimination` that is phrased using 
insertion.
-/
lemma IsCircuit.strong_multi_elimination_insert (x : ι → α) (I : ι → Set α) (z : α)
    (hxI : ∀ i, x i ∉ I i) (hC : ∀ i, M.IsCircuit (insert (x i) (I i)))
    (hJx : M.IsCircuit (J ∪ range x)) (hzJ : z ∈ J) (hzI : ∀ i, z ∉ I i) :
    ∃ C' ⊆ J ∪ ⋃ i, I i, M.IsCircuit C' ∧ z ∈ C' := by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z ∈ M.closure ((⋃ i, I i) ∪ (J \ {z})) by
    rw [mem_closure_iff_exists_isCircuit (by simp [hzI])] at hcl
    obtain ⟨C', hC'ss, hC', hzC'⟩ := hcl
    refine ⟨C', ?_, hC', hzC'⟩
    rwa [union_comm, ← insert_union, insert_sdiff_singleton, insert_eq_of_mem hzJ] at hC'ss
  have hC' (i) : M.closure (I i) = M.closure (insert (x i) (I i)) := by
    simpa [sdiff_singleton_eq_self (hxI _)] using (hC i).closure_sdiff_singleton_eq (x i)
  -- This is true because each `I i` spans `x i` and `(range x) ∪ (J \ {z})` spans `z`.
  rw [closure_union_congr_left <| closure_iUnion_congr _ _ hC',
    iUnion_insert_eq_range_union_iUnion, union_right_comm]
  refine mem_of_mem_of_subset (hJx.mem_closure_sdiff_singleton_of_mem (.inl hzJ))
    (M.closure_subset_closure (subset_trans ?_ subset_union_left))
  rw [union_sdiff_distrib, union_comm]
  exact union_subset_union_left _ sdiff_subset

/-- A generalization of the strong circuit elimination axiom `Matroid.IsCircuit.strong_elimination`
to an infinite collection of circuits.

It states that, given a circuit `C₀`, an arbitrary collection `C : ι → Set α` of circuits,
an element `x i` of `C₀ ∩ C i` for each `i`, and an element `z ∈ C₀` outside all the `C i`,
the union of `C₀` and the `C i` contains a circuit containing `z` but none of the `x i`.

This is one of the axioms when defining infinite matroids via circuits.

TODO : A similar statement will hold even when all mentions of `z` are removed. -/
/-
**Matroid.IsCircuit.strong_multi_elimination** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {ι : Type u_2} {C₀ : Set α},   M.IsCircui
t C₀ →     ∀ (x : ι → α) (C : ι → Set α) (z : α),       (∀ (i : ι), M.IsCircuit 
(C i)) →         (∀ (i : ι), x i ∈ C₀) →           (∀ (i : ι), x i ∈ C i) →     
        (∀ ⦃i i' : ι⦄, x i ∈ C i' → i = i') →               z ∈ C₀ → (∀ (i : ι),
 z ∉ C i) → ∃ C' ⊆ (C₀ ∪ ⋃ i, C i) \ Set.range x, M.IsCircuit C' ∧ z ∈ C'
参数：x : ι → α；C : ι → Set α；z : α；∀ (i : ι), M.IsCircuit (C i)；∀ (i : ι), x i ∈ C
₀；∀ (i : ι), x i ∈ C i；∀ ⦃i i' : ι⦄, x i ∈ C i' → i = i'；∀ (i : ι), z ∉ C i；C₀ ∪
 ⋃ i, C i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.strong_multi_elimination_insert`：∀ {α : Type u_1} {M :
 Matroid α} {ι : Type u_2} {J : Set α} (x : ι → α) (I : ι → Set α) (z : α),   (∀
 (i : ι), x i ∉ I i) →     (∀ (i : ι), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.subset_union_of_subset_right`：subset_union_of_subset_right {s u : Se
t α} (h : s subseteq u) (t : Set α) : s subseteq t union u
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A generalization of the strong circuit elimination axiom `Matroid.IsCircuit.stro
ng_elimination`
to an infinite collection of circuits.

It states that, given a circuit `C₀`, an arbitrary collection `C : ι → Set α` of
 circuits,
an element `x i` of `C₀ ∩ C i` for each `i`, and an element `z ∈ C₀` outside all
 the `C i`,
the union of `C₀` and the `C i` contains a circuit containing `z` but none of th
e `x i`.

This is one of the axioms when defining infinite matroids via circuits.

TODO : A similar statement will hold even when all mentions of `z` are removed.
-/
lemma IsCircuit.strong_multi_elimination (hC₀ : M.IsCircuit C₀) (x : ι → α) (C : ι → Set α) (z : α)
    (hC : ∀ i, M.IsCircuit (C i)) (h_mem_C₀ : ∀ i, x i ∈ C₀) (h_mem : ∀ i, x i ∈ C i)
    (h_unique : ∀ ⦃i i'⦄, x i ∈ C i' → i = i') (hzC₀ : z ∈ C₀) (hzC : ∀ i, z ∉ C i) :
    ∃ C' ⊆ (C₀ ∪ ⋃ i, C i) \ range x, M.IsCircuit C' ∧ z ∈ C' := by
  have hwin := IsCircuit.strong_multi_elimination_insert (M := M) x (fun i ↦ (C i \ {x i}))
    (J := C₀ \ range x) (z := z) (by simp) (fun i ↦ ?_) ?_ ⟨hzC₀, ?_⟩ ?_
  · obtain ⟨C', hC'ss, hC', hzC'⟩ := hwin
    refine ⟨C', hC'ss.trans ?_, hC', hzC'⟩
    refine union_subset (sdiff_subset_sdiff_left subset_union_left)
      (iUnion_subset fun i ↦ subset_sdiff.2
        ⟨sdiff_subset.trans (subset_union_of_subset_right (subset_iUnion ..) _), ?_⟩)
    rw [disjoint_iff_forall_ne]
    rintro _ he _ ⟨j, hj, rfl⟩ rfl
    obtain rfl : j = i := h_unique he.1
    simp at he
  · simpa [insert_eq_of_mem (h_mem i)] using hC i
  · rwa [sdiff_union_self, union_eq_self_of_subset_right]
    rintro _ ⟨i, hi, rfl⟩
    exact h_mem_C₀ i
  · rintro ⟨i, hi, rfl⟩
    exact hzC _ (h_mem i)
  simp only [mem_sdiff, mem_singleton_iff, not_and, not_not]
  exact fun i hzi ↦ (hzC i hzi).elim

/-- A version of `Circuit.strong_multi_elimination` where the collection of circuits is
a `Set (Set α)` and the distinguished elements are a `Set α`, rather than both being indexed. -/
/-
**Matroid.IsCircuit.strong_multi_elimination_set** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C₀ : Set α},   M.IsCircuit C₀ →     ∀ (X
 : Set α) (S : Set (Set α)) (z : α),       (∀ C ∈ S, M.IsCircuit C) →         X 
⊆ C₀ →           (∀ x ∈ X, ∃ C ∈ S, C ∩ X = {x}) → z ∈ C₀ → (∀ C ∈ S, z ∉ C) → ∃
 C' ⊆ (C₀ ∪ ⋃₀ S) \ X, M.IsCircuit C' ∧ z ∈ C'
参数：X : Set α；S : Set (Set α)；z : α；∀ C ∈ S, M.IsCircuit C；∀ x ∈ X, ∃ C ∈ S, C ∩ 
X = {x}；∀ C ∈ S, z ∉ C；C₀ ∪ ⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.strong_multi_elimination`：∀ {α : Type u_1} {M : Matroi
d α} {ι : Type u_2} {C₀ : Set α},   M.IsCircuit C₀ →     ∀ (x : ι → α) (C : ι → 
Set α) (z : α),       (∀ (i : ι)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A version of `Circuit.strong_multi_elimination` where the collection of circuits
 is
a `Set (Set α)` and the distinguished elements are a `Set α`, rather than both b
eing indexed.
-/
lemma IsCircuit.strong_multi_elimination_set (hC₀ : M.IsCircuit C₀) (X : Set α) (S : Set (Set α))
    (z : α) (hCS : ∀ C ∈ S, M.IsCircuit C) (hXC₀ : X ⊆ C₀) (hX : ∀ x ∈ X, ∃ C ∈ S, C ∩ X = {x})
    (hzC₀ : z ∈ C₀) (hz : ∀ C ∈ S, z ∉ C) : ∃ C' ⊆ (C₀ ∪ ⋃₀ S) \ X, M.IsCircuit C' ∧ z ∈ C' := by
  choose! C hC using hX
  simp only [forall_and] at hC
  have hwin := hC₀.strong_multi_elimination (fun x : X ↦ x) (fun x ↦ C x) z ?_ ?_ ?_ ?_ hzC₀ ?_
  · obtain ⟨C', hC'ss, hC', hz⟩ := hwin
    refine ⟨C', hC'ss.trans (sdiff_subset_sdiff (union_subset_union_right _ ?_) (by simp)), hC', hz⟩
    simpa using fun e heX ↦ (subset_sUnion_of_mem (hC.1 e heX))
  · simpa using fun e heX ↦ hCS _ <| hC.1 e heX
  · simpa using fun e heX ↦ hXC₀ heX
  · simp only [Subtype.forall, ← singleton_subset_iff (s := C _)]
    exact fun e heX ↦ by simp [← hC.2 e heX]
  · simp only [Subtype.forall, Subtype.mk.injEq]
    refine fun e heX f hfX hef ↦ ?_
    simpa [hC.2 f hfX] using subset_inter (singleton_subset_iff.2 hef) (singleton_subset_iff.2 heX)
  simpa using fun e heX heC ↦ hz _ (hC.1 e heX) heC

/-- The strong isCircuit elimination axiom. For any pair of distinct circuits `C₁, C₂` and all
`e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
/-
**Matroid.IsCircuit.strong_elimination** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCirc
uit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e f : α} {C₁ C₂ : Set α},   M.IsCircuit 
C₁ → M.IsCircuit C₂ → e ∈ C₁ → e ∈ C₂ → f ∈ C₁ → f ∉ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e},
 M.IsCircuit C ∧ f ∈ C
参数：C₁ ∪ C₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.strong_multi_elimination`：∀ {α : Type u_1} {M : Matroi
d α} {ι : Type u_2} {C₀ : Set α},   M.IsCircuit C₀ →     ∀ (x : ι → α) (C : ι → 
Set α) (z : α),       (∀ (i : ι)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}

--- 原说明 ---
The strong isCircuit elimination axiom. For any pair of distinct circuits `C₁, C
₂` and all
`e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) 
\ {e}`.
-/
lemma IsCircuit.strong_elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (heC₁ : e ∈ C₁)
    (heC₂ : e ∈ C₂) (hfC₁ : f ∈ C₁) (hfC₂ : f ∉ C₂) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C ∧ f ∈ C := by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit ↦ e) (fun _ ↦ C₂) f
    (by simpa) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (sdiff_subset_sdiff (by simp) (by simp)), hC, hfC⟩

/-- The circuit elimination axiom : for any pair of distinct circuits `C₁, C₂` and any `e`,
some circuit is contained in `(C₁ ∪ C₂) \ {e}`.

This is one of the axioms when defining a finitary matroid via circuits;
as an axiom, it is usually stated with the extra assumption that `e ∈ C₁ ∩ C₂`. -/
/-
**Matroid.IsCircuit.elimination** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C₁ C₂ : Set α},   M.IsCircuit C₁ → M.IsC
ircuit C₂ → C₁ ≠ C₂ → ∀ (e : α), ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C
参数：e : α；C₁ ∪ C₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.eq_of_subset_isCircuit`：∀ {α : Type u_1} {M : Matroid 
α} {C C' : Set α}, M.IsCircuit C → M.IsCircuit C' → C ⊆ C' → C = C'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Matroid.IsCircuit.strong_elimination`：∀ {α : Type u_1} {M : Matroid α} {
e f : α} {C₁ C₂ : Set α},   M.IsCircuit C₁ → M.IsCircuit C₂ → e ∈ C₁ → e ∈ C₂ → 
f ∈ C₁ → f ∉ C₂ → ∃ C ⊆ (C…
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t

--- 原说明 ---
The circuit elimination axiom : for any pair of distinct circuits `C₁, C₂` and a
ny `e`,
some circuit is contained in `(C₁ ∪ C₂) \ {e}`.

This is one of the axioms when defining a finitary matroid via circuits;
as an axiom, it is usually stated with the extra assumption that `e ∈ C₁ ∩ C₂`.
-/
lemma IsCircuit.elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C := by
  have hnss : ¬ (C₁ ⊆ C₂) := fun hss ↦ h <| hC₁.eq_of_subset_isCircuit hC₂ hss
  obtain ⟨f, hf₁, hf₂⟩ := not_subset.1 hnss
  by_cases he₁ : e ∈ C₁
  · by_cases he₂ : e ∈ C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subset_sdiff_singleton subset_union_right he₂, hC₂⟩
  exact ⟨C₁, subset_sdiff_singleton subset_union_left he₁, hC₁⟩

end Elimination

/-! ### Finitary Matroids -/
section Finitary

/-
**Matroid.IsCircuit.finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α} [M.Finitary], M.IsCircuit C →
 C.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.indep_iff_forall_finite_subset_indep`：indep_iff_forall_finite_su
bset_indep {M : Matroid α} [Finitary M] : M.Indep I ↔ forall J, J subseteq I -> 
J.Finite -> M.Indep J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsCircuit.eq_of_not_indep_subset`：∀ {α : Type u_1} {M : Matroid 
α} {C X : Set α}, M.IsCircuit C → ¬M.Indep X → X ⊆ C → X = C
-/
lemma IsCircuit.finite [Finitary M] (hC : M.IsCircuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push Not at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]
/-
**Matroid.finitary_iff_forall_isCircuit_finite** 是 Mathlib 中的一个引理，位于命名空间 `Matroi
d`。
形式化陈述：finitary_iff_forall_isCircuit_finite : M.Finitary ↔ forall C, M.IsCircuit 
C -> C.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.finite`：∀ {α : Type u_1} {M : Matroid α} {C : Set α} [
M.Finitary], M.IsCircuit C → C.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.indep_iff_not_dep`：indep_iff_not_dep : M.Indep I ↔ ¬M.Dep I ∧ I 
subseteq M.E
· 使用定理 `Matroid.Dep.exists_isCircuit_subset`：∀ {α : Type u_1} {M : Matroid α} {X
 : Set α}, M.Dep X → ∃ C ⊆ X, M.IsCircuit C
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
lemma finitary_iff_forall_isCircuit_finite : M.Finitary ↔ ∀ C, M.IsCircuit C → C.Finite := by
  refine ⟨fun _ _ ↦ IsCircuit.finite, fun h ↦
    ⟨fun I hI ↦ indep_iff_not_dep.2 ⟨fun hd ↦ ?_,fun x hx ↦ ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
    exact hC.dep.not_indep <| hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

/-- In a finitary matroid, every element spanned by a set `X` is in fact
spanned by a finite independent subset of `X`. -/
/-
**Matroid.exists_mem_finite_closure_of_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Ma
troid`。
形式化陈述：exists_mem_finite_closure_of_mem_closure [M.Finitary] (he : e in M.closure
 X) : exists I subseteq X, I.Finite ∧ M.Indep I ∧ e in M.closure I
参数：he : e in M.closure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用引理 `Matroid.exists_isCircuit_of_mem_closure`：exists_isCircuit_of_mem_closure
 (he : e in M.closure X) (heX : e ∉ X) : exists C subseteq insert e X, M.IsCircu
it C ∧ e in C
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Matroid.IsCircuit.finite`：∀ {α : Type u_1} {M : Matroid α} {C : Set α} [
M.Finitary], M.IsCircuit C → C.Finite
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_indep`：∀ {α : Type u_1} {M : Matroid α
} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.Indep (C \ {e})
· 使用定理 `Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem`：∀ {α : Type u_1} {
M : Matroid α} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → e ∈ M.closure (C \ {
e})

--- 原说明 ---
In a finitary matroid, every element spanned by a set `X` is in fact
spanned by a finite independent subset of `X`.
-/
lemma exists_mem_finite_closure_of_mem_closure [M.Finitary] (he : e ∈ M.closure X) :
    ∃ I ⊆ X, I.Finite ∧ M.Indep I ∧ e ∈ M.closure I := by
  by_cases heY : e ∈ X
  · obtain ⟨J, hJ⟩ := M.exists_isBasis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_isCircuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC.finite.sdiff, hC.sdiff_singleton_indep heC,
    hC.mem_closure_sdiff_singleton_of_mem heC⟩

/-- In a finitary matroid, each finite set `X` spanned by a set `Y` is in fact
spanned by a finite independent subset of `Y`. -/
/-
**Matroid.exists_subset_finite_closure_of_subset_closure** 是 Mathlib 中的一个引理，位于命名
空间 `Matroid`。
形式化陈述：exists_subset_finite_closure_of_subset_closure [M.Finitary] (hX : X.Finite
) (hXY : X subseteq M.closure Y) : exists I subseteq Y, I.Finite ∧ M.Indep I ∧ X
 subseteq M.closure I
参数：hX : X.Finite；hXY : X subseteq M.closure Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on_subset`：∀ {α : Type u} {motive : (s : Set α) → s
.Finite → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ →     (∀ {a : α} {t : 
Set α}, a ∈ s → ∀ (h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Matroid.exists_mem_finite_closure_of_mem_closure`：exists_mem_finite_clos
ure_of_mem_closure [M.Finitary] (he : e in M.closure X) : exists I subseteq X, I
.Finite ∧ M.Indep I ∧ e in M.closure I
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用引理 `Matroid.closure_mono`：closure_mono (M : Matroid α) : Monotone M.closure
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X

--- 原说明 ---
In a finitary matroid, each finite set `X` spanned by a set `Y` is in fact
spanned by a finite independent subset of `Y`.
-/
lemma exists_subset_finite_closure_of_subset_closure [M.Finitary] (hX : X.Finite)
    (hXY : X ⊆ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ X ⊆ M.closure I := by
  suffices aux : ∃ T ⊆ Y, T.Finite ∧ X ⊆ M.closure T by
    obtain ⟨T, hT, hTfin, hXT⟩ := aux
    obtain ⟨I, hI⟩ := M.exists_isBasis' T
    exact ⟨_, hI.subset.trans hT, hTfin.subset hI.subset, hI.indep, by rwa [hI.closure_eq_closure]⟩
  refine Finite.induction_on_subset X hX ⟨∅, by simp⟩ (fun {e Z} heX _ heZ ⟨T, hTY, hTfin, hT⟩ ↦ ?_)
  obtain ⟨S, hSY, hSfin, -, heS⟩ := exists_mem_finite_closure_of_mem_closure (hXY heX)
  exact ⟨S ∪ T, union_subset hSY hTY, hSfin.union hTfin, insert_subset
    (M.closure_mono subset_union_left heS) (hT.trans (M.closure_mono subset_union_right))⟩

end Finitary

/-! ### IsCocircuits -/
section IsCocircuit

variable {K B : Set α}

/-- A cocircuit is a circuit of the dual matroid,
or equivalently the complement of a hyperplane. -/
/-
**Matroid.IsCocircuit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matroid`。
形式化陈述：IsCocircuit (M : Matroid α) (K : Set α) : Prop
参数：M : Matroid α；K : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocircuit is a circuit of the dual matroid,
or equivalently the complement of a hyperplane.
-/
abbrev IsCocircuit (M : Matroid α) (K : Set α) : Prop := M✶.IsCircuit K
/-
**Matroid.isCocircuit_def** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircuit K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircuit K := Iff.rfl
/-
**Matroid.IsCocircuit.isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCocircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K : Set α}, M.IsCocircuit K → M✶.IsCircu
it K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCocircuit.isCircuit (hK : M.IsCocircuit K) : M✶.IsCircuit K :=
  hK
/-
**Matroid.IsCircuit.isCocircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → M✶.IsCocircu
it C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
lemma IsCircuit.isCocircuit (hC : M.IsCircuit C) : M✶.IsCocircuit C := by
  rwa [isCocircuit_def, dual_dual]
/-
**Matroid.IsCocircuit.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCocircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCocircuit C → C.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.nonempty`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}
, M.IsCircuit C → C.Nonempty
· 使用定理 `Matroid.IsCocircuit.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {K : Set
 α}, M.IsCocircuit K → M✶.IsCircuit K
-/
lemma IsCocircuit.nonempty (hC : M.IsCocircuit C) : C.Nonempty :=
  hC.isCircuit.nonempty

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.IsCocircuit.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCocircu
it`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCocircuit C → C ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Matroid.IsCocircuit.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {K : Set
 α}, M.IsCocircuit K → M✶.IsCircuit K
-/
lemma IsCocircuit.subset_ground (hC : M.IsCocircuit C) : C ⊆ M.E :=
  hC.isCircuit.subset_ground
/-
**Matroid.dual_isCocircuit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M✶.IsCocircuit C ↔ M.IsCircu
it C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma dual_isCocircuit_iff : M✶.IsCocircuit C ↔ M.IsCircuit C := by
  rw [isCocircuit_def, dual_dual]
/-
**Matroid.coindep_iff_forall_subset_not_isCocircuit** 是 Mathlib 中的一个引理，位于命名空间 `M
atroid`。
形式化陈述：coindep_iff_forall_subset_not_isCocircuit : M.Coindep X ↔ (forall K, K sub
seteq X -> ¬M.IsCocircuit K) ∧ X subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.indep_iff_forall_subset_not_isCircuit'`：indep_iff_forall_subset_
not_isCircuit' : M.Indep I ↔ (forall C, C subseteq I -> ¬M.IsCircuit C) ∧ I subs
eteq M.E
-/
lemma coindep_iff_forall_subset_not_isCocircuit :
    M.Coindep X ↔ (∀ K, K ⊆ X → ¬M.IsCocircuit K) ∧ X ⊆ M.E :=
  indep_iff_forall_subset_not_isCircuit'

/-- A cocircuit is a minimal set that intersects every base. -/
/-
**Matroid.isCocircuit_iff_minimal** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isCocircuit_iff_minimal : M.IsCocircuit K ↔ Minimal (fun X => forall B, M.
IsBase B -> (X inter B).Nonempty) K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.dual_dep_iff_forall`：dual_dep_iff_forall : (M✶.Dep I) ↔ (forall 
B, M.IsBase B -> (I inter B).Nonempty) ∧ I subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
· 使用引理 `Matroid.isCircuit_def`：isCircuit_def : M.IsCircuit C ↔ Minimal M.Dep C
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `minimal_iff_minimal_of_imp_of_forall`：minimal_iff_minimal_of_imp_of_fora
ll (hPQ : forall ⦃x⦄, Q x -> P x) (h : forall ⦃x⦄, P x -> exists y, y <= x ∧ Q y
) : Minimal P x ↔ Minimal …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
A cocircuit is a minimal set that intersects every base.
-/
lemma isCocircuit_iff_minimal :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ∀ B, M.IsBase B → (X ∩ B).Nonempty) K := by
  have aux : M✶.Dep = fun X ↦ (∀ B, M.IsBase B → (X ∩ B).Nonempty) ∧ X ⊆ M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def, isCircuit_def, aux, iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1) fun X hX ↦
    ⟨X ∩ M.E, inter_subset_left, fun B hB ↦ ?_, inter_subset_right⟩
  rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground]
  exact hX B hB

/-- A cocircuit is a minimal set whose complement is nonspanning. -/
/-
**Matroid.isCocircuit_iff_minimal_compl_nonspanning** 是 Mathlib 中的一个引理，位于命名空间 `M
atroid`。
形式化陈述：isCocircuit_iff_minimal_compl_nonspanning : M.IsCocircuit K ↔ Minimal (fun
 X => ¬ M.Spanning (M.E \ X)) K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_exists_isBase_subset`：spanning_iff_exists_isBase_su
bset (hS : S subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Matroid.isCocircuit_iff_minimal`：isCocircuit_iff_minimal : M.IsCocircuit
 K ↔ Minimal (fun X => forall B, M.IsBase B -> (X inter B).Nonempty) K

--- 原说明 ---
A cocircuit is a minimal set whose complement is nonspanning.
-/
lemma isCocircuit_iff_minimal_compl_nonspanning :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X)) K := by
  convert! isCocircuit_iff_minimal with K
  rw [spanning_iff_exists_isBase_subset]
  simp_rw [not_exists, subset_sdiff, not_and, not_disjoint_iff_nonempty_inter, ← and_imp,
    and_iff_left_of_imp IsBase.subset_ground, inter_comm K]

/-- For an element `e` of a base `B`, the complement of the closure of `B \ {e}` is a cocircuit. -/
/-
**Matroid.IsBase.compl_closure_sdiff_singleton_isCocircuit** 是 Mathlib 中的一个定理，位于
命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {B : Set α}, M.IsBase B → e ∈ B →
 M.IsCocircuit (M.E \ M.closure (B \ {e}))
参数：M.E \ M.closure (B \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_iff_minimal_compl_nonspanning`：isCocircuit_iff_minim
al_compl_nonspanning : M.IsCocircuit K ↔ Minimal (fun X => ¬ M.Spanning (M.E \ X
)) K
· 使用定理 `minimal_subset_iff`：minimal_subset_iff : Minimal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> t subseteq s -> s = t
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Matroid.closure_spanning_iff`：∀ {α : Type u_2} {M : Matroid α} {S : Set 
α},   autoParam (S ⊆ M.E) Matroid.closure_spanning_iff._auto_1 → (M.Spanning (M.
closure S) ↔ M.Spa…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBase_iff_minimal_spanning`：isBase_iff_minimal_spanning : M.IsB
ase B ↔ Minimal M.Spanning B
· 使用定理 `Minimal.notMem_of_prop_sdiff_singleton`：Minimal.notMem_of_prop_sdiff_sin
gleton (h : Minimal P s) (hx : P (s \ {x})) : x ∉ s
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Set.sdiff_subset_comm`：sdiff_subset_comm {s t u : Set α} : s \ t subsete
q u ↔ s \ u subseteq t
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.IsBase.exchange_base_of_notMem_closure`：∀ {α : Type u_2} {M : Ma
troid α} {e f : α} {B : Set α},   M.IsBase B →     e ∈ B →       f ∉ M.closure (
B \ {e}) →         autoParam (f ∈ M.…
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `Matroid.IsBase.spanning`：∀ {α : Type u_2} {M : Matroid α} {B : Set α}, M
.IsBase B → M.Spanning B
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
For an element `e` of a base `B`, the complement of the closure of `B \ {e}` is 
a cocircuit.
-/
lemma IsBase.compl_closure_sdiff_singleton_isCocircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.IsCocircuit (M.E \ M.closure (B \ {e})) := by
  rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_subset_iff,
    sdiff_sdiff_cancel_left (M.closure_subset_ground _),
    closure_spanning_iff (sdiff_subset.trans hB.subset_ground)]
  have hB' := (isBase_iff_minimal_spanning.1 hB)
  refine ⟨fun hsp ↦ hB'.notMem_of_prop_sdiff_singleton hsp he, fun X hX hXss ↦ hXss.antisymm' ?_⟩
  rw [sdiff_subset_comm]
  refine fun f hf ↦ by_contra fun fcl ↦ hX ?_
  rw [subset_sdiff] at hXss
  suffices hsp : M.IsBase (insert f (B \ {e})) by
    refine hsp.spanning.superset <| insert_subset hf <|
      (M.subset_closure _ (sdiff_subset.trans hB.subset_ground)).trans ?_
    rw [subset_sdiff, and_iff_left hXss.2.symm]
    apply closure_subset_ground
  exact hB.exchange_base_of_notMem_closure he fcl

@[deprecated (since := "2026-06-03")]
alias IsBase.compl_closure_diff_singleton_isCocircuit :=
  IsBase.compl_closure_sdiff_singleton_isCocircuit

/-- A version of `Matroid.isCocircuit_iff_minimal_compl_nonspanning` with a support assumption
in the minimality. -/
/-
**Matroid.isCocircuit_iff_minimal_compl_nonspanning'** 是 Mathlib 中的一个引理，位于命名空间 `
Matroid`。
形式化陈述：isCocircuit_iff_minimal_compl_nonspanning' : M.IsCocircuit K ↔ Minimal (fu
n X => ¬ M.Spanning (M.E \ X) ∧ X subseteq M.E) K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_iff_minimal_compl_nonspanning`：isCocircuit_iff_minim
al_compl_nonspanning : M.IsCocircuit K ↔ Minimal (fun X => ¬ M.Spanning (M.E \ X
)) K
· 使用定理 `minimal_iff_minimal_of_imp_of_forall`：minimal_iff_minimal_of_imp_of_fora
ll (hPQ : forall ⦃x⦄, Q x -> P x) (h : forall ⦃x⦄, P x -> exists y, y <= x ∧ Q y
) : Minimal P x ↔ Minimal …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
A version of `Matroid.isCocircuit_iff_minimal_compl_nonspanning` with a support 
assumption
in the minimality.
-/
lemma isCocircuit_iff_minimal_compl_nonspanning' :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X) ∧ X ⊆ M.E) K := by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1)
    (fun X hX ↦ ⟨X ∩ M.E, inter_subset_left, by rwa [sdiff_inter_self_eq_sdiff],
      inter_subset_right⟩)

/-- A cocircuit and a circuit cannot meet in exactly one element. -/
/-
**Matroid.IsCircuit.inter_isCocircuit_ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ma
troid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α} {e : α} {K : Set α}, M.IsCirc
uit C → M.IsCocircuit K → C ∩ K ≠ {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.sdiff_singleton_ssubset`：sdiff_singleton_ssubset : s \ {a} ⊂ s ↔ a i
n s
· 使用引理 `Matroid.spanning_iff_ground_subset_closure`：spanning_iff_ground_subset_c
losure (hS : S subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matroid.Spanning.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {S : Set α
}, M.Spanning S → M.closure S = M.E
· 使用定理 `Set.sdiff_sdiff_eq_sdiff_union`：sdiff_sdiff_eq_sdiff_union (h : u subset
eq s) : s \ (t \ u) = s \ t union u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Matroid.closure_union_congr_right`：closure_union_congr_right {Y' : Set α
} (h : M.closure Y = M.closure Y') : M.closure (X union Y) = M.closure (X union 
Y')
· 使用定理 `Matroid.IsCircuit.closure_sdiff_singleton_eq`：∀ {α : Type u_1} {M : Matr
oid α} {C : Set α}, M.IsCircuit C → ∀ (e : α), M.closure (C \ {e}) = M.closure C
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A cocircuit and a circuit cannot meet in exactly one element.
-/
lemma IsCircuit.inter_isCocircuit_ne_singleton (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    C ∩ K ≠ {e} := by
  intro he
  have heC : e ∈ C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (sdiff_singleton_ssubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  nth_rw 1 [← hKe.closure_eq, sdiff_sdiff_eq_sdiff_union]
  · refine (M.closure_subset_closure (subset_union_left (t := C))).trans ?_
    rw [union_assoc, singleton_union, insert_eq_of_mem heC, ← closure_union_congr_right
      (hC.closure_sdiff_singleton_eq e), union_eq_self_of_subset_right]
    rw [← he, sdiff_self_inter]
    exact sdiff_subset_sdiff_left hC.subset_ground
  rw [← he]
  exact inter_subset_left.trans hC.subset_ground
/-
**Matroid.IsCircuit.isCocircuit_inter_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C K : Set α}, M.IsCircuit C → M.IsCocirc
uit K → (C ∩ K).Nonempty → (C ∩ K).Nontrivial
参数：C ∩ K；C ∩ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.nontrivial_iff_ne_singleton`：nontrivial_iff_ne_singleton (ha : a in 
s) : s.Nontrivial ↔ s != {a}
· 使用定理 `Matroid.IsCircuit.inter_isCocircuit_ne_singleton`：∀ {α : Type u_1} {M : 
Matroid α} {C : Set α} {e : α} {K : Set α}, M.IsCircuit C → M.IsCocircuit K → C 
∩ K ≠ {e}
-/
lemma IsCircuit.isCocircuit_inter_nontrivial (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
    (hCK : (C ∩ K).Nonempty) : (C ∩ K).Nontrivial := by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK
/-
**Matroid.IsCircuit.isCocircuit_disjoint_or_nontrivial_inter** 是 Mathlib 中的一个定理，
位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C K : Set α}, M.IsCircuit C → M.IsCocirc
uit K → Disjoint C K ∨ (C ∩ K).Nontrivial
参数：C ∩ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Matroid.IsCircuit.isCocircuit_inter_nontrivial`：∀ {α : Type u_1} {M : Ma
troid α} {C K : Set α}, M.IsCircuit C → M.IsCocircuit K → (C ∩ K).Nonempty → (C 
∩ K).Nontrivial
-/
lemma IsCircuit.isCocircuit_disjoint_or_nontrivial_inter (hC : M.IsCircuit C)
    (hK : M.IsCocircuit K) : Disjoint C K ∨ (C ∩ K).Nontrivial := by
  rw [or_iff_not_imp_left, disjoint_iff_inter_eq_empty, ← ne_eq, ← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK
/-
**Matroid.dual_rankPos_iff_exists_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_rankPos_iff_exists_isCircuit : M✶.RankPos ↔ exists C, M.IsCircuit C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.rankPos_iff`：∀ {α : Type u_1} (M : Matroid α), M.RankPos ↔ ¬M.Is
Base ∅
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ground_indep_iff_isBase`：ground_indep_iff_isBase : M.Indep M.E ↔
 M.IsBase M.E
· 使用引理 `Matroid.indep_iff_forall_subset_not_isCircuit`：indep_iff_forall_subset_n
ot_isCircuit (hI : I subseteq M.E
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
-/
lemma dual_rankPos_iff_exists_isCircuit : M✶.RankPos ↔ ∃ C, M.IsCircuit C := by
  rw [rankPos_iff, dual_isBase_iff, sdiff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_isBase, indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩
/-
**Matroid.IsCircuit.dual_rankPos** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → M✶.RankPos
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.dual_rankPos_iff_exists_isCircuit`：dual_rankPos_iff_exists_isCir
cuit : M✶.RankPos ↔ exists C, M.IsCircuit C
-/
lemma IsCircuit.dual_rankPos (hC : M.IsCircuit C) : M✶.RankPos :=
  dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩
/-
**Matroid.exists_isCircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：exists_isCircuit [RankPos M✶] : exists C, M.IsCircuit C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.dual_rankPos_iff_exists_isCircuit`：dual_rankPos_iff_exists_isCir
cuit : M✶.RankPos ↔ exists C, M.IsCircuit C
-/
lemma exists_isCircuit [RankPos M✶] : ∃ C, M.IsCircuit C :=
  dual_rankPos_iff_exists_isCircuit.1 (by assumption)
/-
**Matroid.rankPos_iff_exists_isCocircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：rankPos_iff_exists_isCocircuit : M.RankPos ↔ exists K, M.IsCocircuit K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用引理 `Matroid.dual_rankPos_iff_exists_isCircuit`：dual_rankPos_iff_exists_isCir
cuit : M✶.RankPos ↔ exists C, M.IsCircuit C
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rankPos_iff_exists_isCocircuit : M.RankPos ↔ ∃ K, M.IsCocircuit K := by
  rw [← dual_dual M, dual_rankPos_iff_exists_isCircuit, dual_dual M]

/-- The fundamental cocircuit for `B` and `e`:
that is, the unique cocircuit `K` of `M` for which `K ∩ B = {e}`.
Should be used when `B` is a base and `e ∈ B`.
Has the junk value `{e}` if `e ∉ B` or `e ∉ M.E`. -/
/-
**Matroid.fundCocircuit** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：fundCocircuit (M : Matroid α) (e : α) (B : Set α)
参数：M : Matroid α；e : α；B : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fundamental cocircuit for `B` and `e`:
that is, the unique cocircuit `K` of `M` for which `K ∩ B = {e}`.
Should be used when `B` is a base and `e ∈ B`.
Has the junk value `{e}` if `e ∉ B` or `e ∉ M.E`.
-/
def fundCocircuit (M : Matroid α) (e : α) (B : Set α) := M✶.fundCircuit e (M✶.E \ B)
/-
**Matroid.fundCocircuit_isCocircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCocircuit_isCocircuit (he : e in B) (hB : M.IsBase B) : M.IsCocircuit 
M.fundCocircuit e B
参数：he : e in B；hB : M.IsBase B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.fundCircuit_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {I
 : Set α} {e : α},   M.Indep I → e ∈ M.closure I → e ∉ I → M.IsCircuit (M.fundCi
rcuit e I)
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Matroid.IsBase.compl_isBase_dual`：∀ {α : Type u_1} {M : Matroid α} {B : 
Set α}, M.IsBase B → M✶.IsBase (M.E \ B)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma fundCocircuit_isCocircuit (he : e ∈ B) (hB : M.IsBase B) :
    M.IsCocircuit <| M.fundCocircuit e B := by
  apply hB.compl_isBase_dual.indep.fundCircuit_isCircuit _ (by simp [he])
  rw [hB.compl_isBase_dual.closure_eq, dual_ground]
  exact hB.subset_ground he
/-
**Matroid.mem_fundCocircuit** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：mem_fundCocircuit (M : Matroid α) (e : α) (B : Set α) : e in M.fundCocircu
it e B
参数：M : Matroid α；e : α；B : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
lemma mem_fundCocircuit (M : Matroid α) (e : α) (B : Set α) : e ∈ M.fundCocircuit e B :=
  mem_insert _ _
/-
**Matroid.fundCocircuit_subset_insert_compl** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCocircuit_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) : M.
fundCocircuit e B subseteq insert e (M.E \ B)
参数：M : Matroid α；e : α；B : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.fundCircuit_subset_insert`：fundCircuit_subset_insert (M : Matroi
d α) (e : α) (I : Set α) : M.fundCircuit e I subseteq insert e I
-/
lemma fundCocircuit_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) :
    M.fundCocircuit e B ⊆ insert e (M.E \ B) :=
  fundCircuit_subset_insert ..
/-
**Matroid.fundCocircuit_inter_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCocircuit_inter_eq (M : Matroid α) {B : Set α} (he : e in B) : (M.fund
Cocircuit e B) inter B = {e}
参数：M : Matroid α；he : e in B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用引理 `Matroid.fundCocircuit_subset_insert_compl`：fundCocircuit_subset_insert_c
ompl (M : Matroid α) (e : α) (B : Set α) : M.fundCocircuit e B subseteq insert e
 (M.E \ B)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `Matroid.mem_fundCocircuit`：mem_fundCocircuit (M : Matroid α) (e : α) (B 
: Set α) : e in M.fundCocircuit e B
-/
lemma fundCocircuit_inter_eq (M : Matroid α) {B : Set α} (he : e ∈ B) :
    (M.fundCocircuit e B) ∩ B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocircuit _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocircuit_subset_insert_compl _ _)).trans ?_
  simp +contextual

/-- The fundamental cocircuit of `X` and `e` has the junk value `{e}` if `e ∉ M.E` -/
/-
**Matroid.fundCocircuit_eq_of_notMem_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCocircuit_eq_of_notMem_ground (X : Set α) (he : e ∉ M.E) : M.fundCocir
cuit e X = {e}
参数：X : Set α；he : e ∉ M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.fundCocircuit.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α) (B 
: Set α), M.fundCocircuit e B = M✶.fundCircuit e (M✶.E \ B)
· 使用引理 `Matroid.fundCircuit_eq_of_notMem_ground`：fundCircuit_eq_of_notMem_ground
 (heX : e ∉ M.E) : M.fundCircuit e X = {e}

--- 原说明 ---
The fundamental cocircuit of `X` and `e` has the junk value `{e}` if `e ∉ M.E`
-/
lemma fundCocircuit_eq_of_notMem_ground (X : Set α) (he : e ∉ M.E) :
    M.fundCocircuit e X = {e} := by
  rwa [fundCocircuit, fundCircuit_eq_of_notMem_ground]

/-- The fundamental cocircuit of `X` and `e` has the junk value `{e}` if `e ∉ X` -/
/-
**Matroid.fundCocircuit_eq_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：fundCocircuit_eq_of_notMem (M : Matroid α) (heX : e ∉ X) : M.fundCocircuit
 e X = {e}
参数：M : Matroid α；heX : e ∉ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.fundCocircuit.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α) (B 
: Set α), M.fundCocircuit e B = M✶.fundCircuit e (M✶.E \ B)
· 使用引理 `Matroid.fundCircuit_eq_of_mem`：fundCircuit_eq_of_mem (heX : e in X) : M.
fundCircuit e X = {e}
· 使用引理 `Matroid.fundCocircuit_eq_of_notMem_ground`：fundCocircuit_eq_of_notMem_gr
ound (X : Set α) (he : e ∉ M.E) : M.fundCocircuit e X = {e}

--- 原说明 ---
The fundamental cocircuit of `X` and `e` has the junk value `{e}` if `e ∉ X`
-/
lemma fundCocircuit_eq_of_notMem (M : Matroid α) (heX : e ∉ X) : M.fundCocircuit e X = {e} := by
  by_cases he : e ∈ M.E
  · rw [fundCocircuit, fundCircuit_eq_of_mem]
    exact ⟨he, heX⟩
  rw [fundCocircuit_eq_of_notMem_ground _ he]

/-- For every element `e` of an independent set `I`,
there is a cocircuit whose intersection with `I` is `{e}`. -/
/-
**Matroid.Indep.exists_isCocircuit_inter_eq_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {e : α}, M.Indep I → e ∈ I → 
∃ K, M.IsCocircuit K ∧ K ∩ I = {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用引理 `Matroid.fundCocircuit_isCocircuit`：fundCocircuit_isCocircuit (he : e in 
B) (hB : M.IsBase B) : M.IsCocircuit M.fundCocircuit e B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `Matroid.mem_fundCocircuit`：mem_fundCocircuit (M : Matroid α) (e : α) (B 
: Set α) : e in M.fundCocircuit e B
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.fundCocircuit_inter_eq`：fundCocircuit_inter_eq (M : Matroid α) {
B : Set α} (he : e in B) : (M.fundCocircuit e B) inter B = {e}
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t

--- 原说明 ---
For every element `e` of an independent set `I`,
there is a cocircuit whose intersection with `I` is `{e}`.
-/
lemma Indep.exists_isCocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.IsCocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_isCocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocircuit _ _ _), singleton_subset_iff, and_iff_left heI,
    ← M.fundCocircuit_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB

/-- Fundamental circuits and cocircuits of a base `B` play dual roles;
`e` belongs to the fundamental cocircuit for `B` and `f` if and only if
`f` belongs to the fundamental circuit for `e` and `B`.
This statement isn't so reasonable unless `f ∈ B` and `e ∉ B`,
but holds due to junk values even without these assumptions. -/
/-
**Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit** 是 Mathlib 中的一个定理，位于命名空间
 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} {e f : α}, M.IsBase B → (e ∈ 
M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B)
参数：e ∈ M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.IsBase.compl_isBase_dual`：∀ {α : Type u_1} {M : Matroid α} {B : 
Set α}, M.IsBase B → M✶.IsBase (M.E \ B)
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.fundCircuit_eq_of_notMem_ground`：fundCircuit_eq_of_notMem_ground
 (heX : e ∉ M.E) : M.fundCircuit e X = {e}
· 使用定理 `Matroid.fundCocircuit.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α) (B 
: Set α), M.fundCocircuit e B = M✶.fundCircuit e (M✶.E \ B)
· 使用引理 `Matroid.fundCircuit_eq_of_mem`：fundCircuit_eq_of_mem (heX : e in X) : M.
fundCircuit e X = {e}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `Matroid.fundCocircuit_subset_insert_compl`：fundCocircuit_subset_insert_c
ompl (M : Matroid α) (e : α) (B : Set α) : M.fundCocircuit e B subseteq insert e
 (M.E \ B)
· 使用定理 `Matroid.Indep.mem_fundCircuit_iff`：∀ {α : Type u_1} {M : Matroid α} {I :
 Set α} {e x : α},   M.Indep I → e ∈ M.closure I → e ∉ I → (x ∈ M.fundCircuit e 
I ↔ M.Indep (insert e I…
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
· 使用定理 `Matroid.IsBase.compl_isBase_of_dual`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M✶.IsBase B → M.IsBase (M.E \ B)
· 使用定理 `Matroid.IsBase.exchange_isBase_of_indep'`：∀ {α : Type u_1} {M : Matroid 
α} {B : Set α} {e f : α},   M.IsBase B → e ∈ B → f ∉ B → M.Indep (insert f B \ {
e}) → M.IsBase (insert f B \ {…
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.sdiff_sdiff_right`：sdiff_sdiff_right {s t u : Set α} : s \ (t \ u) =
 s \ t union s inter u
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Fundamental circuits and cocircuits of a base `B` play dual roles;
`e` belongs to the fundamental cocircuit for `B` and `f` if and only if
`f` belongs to the fundamental circuit for `e` and `B`.
This statement isn't so reasonable unless `f ∈ B` and `e ∉ B`,
but holds due to junk values even without these assumptions.
-/
lemma IsBase.mem_fundCocircuit_iff_mem_fundCircuit {e f : α} (hB : M.IsBase B) :
    e ∈ M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B := by
  -- By symmetry and duality, it suffices to show the implication in one direction.
  suffices aux : ∀ {N : Matroid α} {B' : Set α} (hB' : N.IsBase B') {e f},
      e ∈ N.fundCocircuit f B' → f ∈ N.fundCircuit e B' from
    ⟨fun h ↦ aux hB h, fun h ↦ aux hB.compl_isBase_dual <| by
      simpa [fundCocircuit, inter_eq_self_of_subset_right hB.subset_ground]⟩
  clear! B M e f
  intro M B hB e f he
  -- discharge the various degenerate cases.
  obtain rfl | hne := eq_or_ne e f
  · simp [mem_fundCircuit]
  have hB' : M✶.IsBase (M✶.E \ B) := hB.compl_isBase_dual
  obtain hfE | hfE := em' <| f ∈ M.E
  · rw [fundCocircuit, fundCircuit_eq_of_notMem_ground (by simpa)] at he
    contradiction
  obtain hfB | hfB := em' <| f ∈ B
  · rw [fundCocircuit, fundCircuit_eq_of_mem (by simp [hfE, hfB])] at he
    contradiction
  obtain ⟨heE, heB⟩ : e ∈ M.E \ B := by
    simpa [hne] using (M.fundCocircuit_subset_insert_compl f B) he
  -- Use basis exchange to argue the equivalence.
  rw [fundCocircuit, hB'.indep.mem_fundCircuit_iff (by rwa [hB'.closure_eq]) (by simp [hfB])] at he
  rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) heB]
  have hB' : M.IsBase (M.E \ (insert f (M✶.E \ B) \ {e})) :=
    (hB'.exchange_isBase_of_indep' ⟨heE, heB⟩ (by simp [hfE, hfB]) he).compl_isBase_of_dual
  refine hB'.indep.subset ?_
  simp only [dual_ground, sdiff_singleton_subset_iff]
  rw [sdiff_sdiff_right, inter_eq_self_of_subset_right (by simpa), union_singleton, insert_comm,
    ← union_singleton (s := M.E \ B), ← sdiff_sdiff, sdiff_sdiff_cancel_left hB.subset_ground]
  simp [hfB]

end IsCocircuit

end Matroid

