/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-! # Cylinders with closed compact bases

We define the set of all cylinders with closed compact bases. Those sets play a role in the
proof of Kolmogorov's extension theorem.

## Main definitions

* `closedCompactCylinders X`: the set of all cylinders of `Π i, X i` based on closed compact sets.

## Main statements

* `mem_measurableCylinders_of_mem_closedCompactCylinders`: in a topological space with second
  countable topology and measurable open sets, a set in `closedCompactCylinders X` is a measurable
  cylinder.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {t : Set (Π i, X i)}

variable (X) in
/-- The set of all cylinders based on closed compact sets. Note that such a set is closed, but
not compact in general (for instance, the whole space is always a closed compact cylinder). -/
/-
**MeasureTheory.closedCompactCylinders** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`
。
形式化陈述：closedCompactCylinders : Set (Set (Π i, X i))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all cylinders based on closed compact sets. Note that such a set is c
losed, but
not compact in general (for instance, the whole space is always a closed compact
 cylinder).
-/
def closedCompactCylinders : Set (Set (Π i, X i)) :=
  ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

variable (X) in
/-
**MeasureTheory.empty_mem_closedCompactCylinders** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：empty_mem_closedCompactCylinders : ∅ in closedCompactCylinders X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.cylinder_empty`：cylinder_empty (s : Finset ι) : cylinder s
 (∅ : Set (forall i : s, α i)) = ∅
-/
theorem empty_mem_closedCompactCylinders : ∅ ∈ closedCompactCylinders X := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩
/-
**MeasureTheory.mem_closedCompactCylinders** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：mem_closedCompactCylinders (t : Set (Π i, X i)) : t in closedCompactCylind
ers X ↔ exists (s S : _), IsClosed S ∧ IsCompact S ∧ t = cylinder s S
参数：t : Set (Π i, X i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closedCompactCylinders (t : Set (Π i, X i)) :
    t ∈ closedCompactCylinders X
      ↔ ∃ (s S : _), IsClosed S ∧ IsCompact S ∧ t = cylinder s S := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff, exists_prop]

/-- A finset `s` such that `t = cylinder s S`. `S` is given by `closedCompactCylinders.set`. -/
/-
**MeasureTheory.closedCompactCylinders.finset** 是 Mathlib 中的一个定义，位于命名空间 `Measure
Theory.closedCompactCylinders`。
形式化陈述：{ι : Type u_1} →   {X : ι → Type u_2} →     [inst : (i : ι) → TopologicalS
pace (X i)] →       {t : Set ((i : ι) → X i)} → t ∈ MeasureTheory.closedCompactC
ylinders X → Finset ι
参数：i : ι；X i；(i : ι) → X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finset `s` such that `t = cylinder s S`. `S` is given by `closedCompactCylinde
rs.set`.
-/
noncomputable def closedCompactCylinders.finset (ht : t ∈ closedCompactCylinders X) :
    Finset ι :=
  ((mem_closedCompactCylinders t).mp ht).choose

/-- A set `S` such that `t = cylinder s S`. `s` is given by `closedCompactCylinders.finset`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.closedCompactCylinders.set** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.closedCompactCylinders`。
形式化陈述：{ι : Type u_1} →   {X : ι → Type u_2} →     [inst : (i : ι) → TopologicalS
pace (X i)] →       {t : Set ((i : ι) → X i)} →         (ht : t ∈ MeasureTheory.
closedCompactCylinders X) →           Set ((i : ↥(MeasureTheory.closedCompactCyl
inders.finset ht)) → X ↑i)
参数：i : ι；X i；(i : ι) → X i；ht : t ∈ MeasureTheory.closedCompactCylinders X；(i : 
↥(MeasureTheory.closedCompactCylinders.finset ht)) → X ↑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def closedCompactCylinders.set (ht : t ∈ closedCompactCylinders X) :
    Set (Π i : closedCompactCylinders.finset ht, X i) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose
/-
**MeasureTheory.closedCompactCylinders.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.closedCompactCylinders`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i : ι) → TopologicalSpace (X 
i)] {t : Set ((i : ι) → X i)}   (ht : t ∈ MeasureTheory.closedCompactCylinders X
), IsClosed (MeasureTheory.closedCompactCylinders.set ht)
参数：i : ι；X i；(i : ι) → X i；ht : t ∈ MeasureTheory.closedCompactCylinders X；Measu
reTheory.closedCompactCylinders.set ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_closedCompactCylinders`：mem_closedCompactCylinders (t 
: Set (Π i, X i)) : t in closedCompactCylinders X ↔ exists (s S : _), IsClosed S
 ∧ IsCompact S ∧ t = cylinder …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem closedCompactCylinders.isClosed (ht : t ∈ closedCompactCylinders X) :
    IsClosed (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.1
/-
**MeasureTheory.closedCompactCylinders.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.closedCompactCylinders`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i : ι) → TopologicalSpace (X 
i)] {t : Set ((i : ι) → X i)}   (ht : t ∈ MeasureTheory.closedCompactCylinders X
), IsCompact (MeasureTheory.closedCompactCylinders.set ht)
参数：i : ι；X i；(i : ι) → X i；ht : t ∈ MeasureTheory.closedCompactCylinders X；Measu
reTheory.closedCompactCylinders.set ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_closedCompactCylinders`：mem_closedCompactCylinders (t 
: Set (Π i, X i)) : t in closedCompactCylinders X ↔ exists (s S : _), IsClosed S
 ∧ IsCompact S ∧ t = cylinder …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem closedCompactCylinders.isCompact (ht : t ∈ closedCompactCylinders X) :
    IsCompact (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.1
/-
**MeasureTheory.closedCompactCylinders.eq_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.closedCompactCylinders`。
形式化陈述：∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i : ι) → TopologicalSpace (X 
i)] {t : Set ((i : ι) → X i)}   (ht : t ∈ MeasureTheory.closedCompactCylinders X
),   t =     MeasureTheory.cylinder (MeasureTheory.closedCompactCylinders.finset
 ht)       (MeasureTheory.closedCompactCylinders.set ht)
参数：i : ι；X i；(i : ι) → X i；ht : t ∈ MeasureTheory.closedCompactCylinders X；Measu
reTheory.closedCompactCylinders.finset ht；MeasureTheory.closedCompactCylinders.s
et ht。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_closedCompactCylinders`：mem_closedCompactCylinders (t 
: Set (Π i, X i)) : t in closedCompactCylinders X ↔ exists (s S : _), IsClosed S
 ∧ IsCompact S ∧ t = cylinder …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem closedCompactCylinders.eq_cylinder (ht : t ∈ closedCompactCylinders X) :
    t = cylinder (closedCompactCylinders.finset ht) (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.2
/-
**MeasureTheory.cylinder_mem_closedCompactCylinders** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (Π i : s, X i)
) (hS_closed : IsClosed S) (hS_compact : IsCompact S) : cylinder s S in closedCo
mpactCylinders X
参数：s : Finset ι；S : Set (Π i : s, X i)；hS_closed : IsClosed S；hS_compact : IsCom
pact S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_closedCompactCylinders`：mem_closedCompactCylinders (t 
: Set (Π i, X i)) : t in closedCompactCylinders X ↔ exists (s S : _), IsClosed S
 ∧ IsCompact S ∧ t = cylinder …
-/
theorem cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (Π i : s, X i))
    (hS_closed : IsClosed S) (hS_compact : IsCompact S) :
    cylinder s S ∈ closedCompactCylinders X := by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩
/-
**MeasureTheory.mem_measurableCylinders_of_mem_closedCompactCylinders** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mem_measurableCylinders_of_mem_closedCompactCylinders [forall i, Measurabl
eSpace (X i)] [forall i, SecondCountableTopology (X i)] [forall i, OpensMeasurab
leSpace (X i)] (ht : t in closedCompactCylinders X) : t in measurableCylinders X
参数：X i；X i；X i；ht : t in closedCompactCylinders X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.closedCompactCylinders.isClosed`：∀ {ι : Type u_1} {X : ι →
 Type u_2} [inst : (i : ι) → TopologicalSpace (X i)] {t : Set ((i : ι) → X i)}  
 (ht : t ∈ MeasureTheory.closedComp…
· 使用定理 `MeasureTheory.closedCompactCylinders.eq_cylinder`：∀ {ι : Type u_1} {X : 
ι → Type u_2} [inst : (i : ι) → TopologicalSpace (X i)] {t : Set ((i : ι) → X i)
}   (ht : t ∈ MeasureTheory.closedComp…
-/
theorem mem_measurableCylinders_of_mem_closedCompactCylinders [∀ i, MeasurableSpace (X i)]
    [∀ i, SecondCountableTopology (X i)] [∀ i, OpensMeasurableSpace (X i)]
    (ht : t ∈ closedCompactCylinders X) :
    t ∈ measurableCylinders X := by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

end MeasureTheory

