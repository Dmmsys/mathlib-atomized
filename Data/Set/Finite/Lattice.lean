/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Lattice.Image

import Mathlib.Data.Fintype.Option

/-!
# Finiteness of unions and intersections

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

@[expose] public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/-
**Set.fintypeiUnion** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeiUnion [DecidableEq α] [Fintype (PLift ι)] (f : ι -> Set α) [forall
 i, Fintype (f i)] : Fintype (⋃ i, f i)
参数：PLift ι；f : ι -> Set α；f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeiUnion [DecidableEq α] [Fintype (PLift ι)] (f : ι → Set α) [∀ i, Fintype (f i)] :
    Fintype (⋃ i, f i) :=
  Fintype.ofFinset (Finset.univ.biUnion fun i : PLift ι => (f i.down).toFinset) <| by simp
/-
**Set.fintypesUnion** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypesUnion [DecidableEq α] {s : Set (Set α)} [Fintype s] [H : forall t 
: s, Fintype (t : Set α)] : Fintype (⋃₀ s)
参数：Set α；t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypesUnion [DecidableEq α] {s : Set (Set α)} [Fintype s]
    [H : ∀ t : s, Fintype (t : Set α)] : Fintype (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Set.fintypeiUnion _ _ _ _ _ H
/-
**Set.toFinset_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：toFinset_iUnion [Fintype β] [DecidableEq α] (f : β -> Set α) [forall w, Fi
ntype (f w)] : Set.toFinset (⋃ (x : β), f x) = Finset.biUnion (Finset.univ : Fin
set β) (fun x => (f x).toFinset)
参数：f : β -> Set α；f w。
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toFinset_iUnion [Fintype β] [DecidableEq α] (f : β → Set α)
    [∀ w, Fintype (f w)] :
    Set.toFinset (⋃ (x : β), f x) =
    Finset.biUnion (Finset.univ : Finset β) (fun x => (f x).toFinset) := by
  ext v
  simp only [mem_toFinset, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- A union of sets with `Fintype` structure over a set with `Fintype` structure has a `Fintype`
structure. -/
@[instance_reducible]
/-
**Set.fintypeBiUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeBiUnion [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι 
-> Set α) (H : forall i in s, Fintype (t i)) : Fintype (⋃ x in s, t x)
参数：s : Set ι；t : ι -> Set α；H : forall i in s, Fintype (t i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A union of sets with `Fintype` structure over a set with `Fintype` structure has
 a `Fintype`
structure.
-/
def fintypeBiUnion [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι → Set α)
    (H : ∀ i ∈ s, Fintype (t i)) : Fintype (⋃ x ∈ s, t x) :=
  haveI : ∀ i : toFinset s, Fintype (t i) := fun i => H i (mem_toFinset.1 i.2)
  Fintype.ofFinset (s.toFinset.attach.biUnion fun x => (t x).toFinset) fun x => by simp
/-
**Set.fintypeBiUnion'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeBiUnion' [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι
 -> Set α) [forall i, Fintype (t i)] : Fintype (⋃ x in s, t x)
参数：s : Set ι；t : ι -> Set α；t i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeBiUnion' [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι → Set α)
    [∀ i, Fintype (t i)] : Fintype (⋃ x ∈ s, t x) :=
  Fintype.ofFinset (s.toFinset.biUnion fun x => (t x).toFinset) <| by simp

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/-
**Finite.Set.finite_iUnion** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_iUnion [Finite ι] (f : ι -> Set α) [forall i, Finite (f i)] : Finit
e (⋃ i, f i)
参数：f : ι -> Set α；f i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
-/
instance finite_iUnion [Finite ι] (f : ι → Set α) [∀ i, Finite (f i)] : Finite (⋃ i, f i) := by
  have : Fintype (PLift ι) := Fintype.ofFinite _
  have : ∀ i, Fintype (f i) := fun i => Fintype.ofFinite _
  classical apply (fintypeiUnion _).finite
/-
**Finite.Set.finite_sUnion** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_sUnion {s : Set (Set α)} [Finite s] [H : forall t : s, Finite (t : 
Set α)] : Finite (⋃₀ s)
参数：Set α；t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
-/
instance finite_sUnion {s : Set (Set α)} [Finite s] [H : ∀ t : s, Finite (t : Set α)] :
    Finite (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Finite.Set.finite_iUnion _ _ _ _ H
/-
**Finite.Set.finite_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finite.Set`。
形式化陈述：finite_biUnion {ι : Type*} (s : Set ι) [Finite s] (t : ι -> Set α) (H : fo
rall i in s, Finite (t i)) : Finite (⋃ x in s, t x)
参数：s : Set ι；t : ι -> Set α；H : forall i in s, Finite (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem finite_biUnion {ι : Type*} (s : Set ι) [Finite s] (t : ι → Set α)
    (H : ∀ i ∈ s, Finite (t i)) : Finite (⋃ x ∈ s, t x) := by
  rw [biUnion_eq_iUnion]
  have : ∀ i : s, Finite (t i) := fun i => H i i.property
  infer_instance
/-
**Finite.Set.finite_biUnion'** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_biUnion' {ι : Type*} (s : Set ι) [Finite s] (t : ι -> Set α) [foral
l i, Finite (t i)] : Finite (⋃ x in s, t x)
参数：s : Set ι；t : ι -> Set α；t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.Set.finite_biUnion`：finite_biUnion {ι : Type*} (s : Set ι) [Finit
e s] (t : ι -> Set α) (H : forall i in s, Finite (t i)) : Finite (⋃ x in s, t x)
-/
instance finite_biUnion' {ι : Type*} (s : Set ι) [Finite s] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋃ x ∈ s, t x) :=
  finite_biUnion s t fun _ _ => inferInstance

/-- Example: `Finite (⋃ (i < n), f i)` where `f : ℕ → Set α` and `[∀ i, Finite (f i)]`
(when given instances from `Order.Interval.Finset.Nat`).
-/
/-
**Finite.Set.finite_biUnion''** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_biUnion'' {ι : Type*} (p : ι -> Prop) [h : Finite { x | p x }] (t :
 ι -> Set α) [forall i, Finite (t i)] : Finite (⋃ (x) (_ : p x), t x)
参数：p : ι -> Prop；t : ι -> Set α；t i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Example: `Finite (⋃ (i < n), f i)` where `f : ℕ → Set α` and `[∀ i, Finite (f i)
]`
(when given instances from `Order.Interval.Finset.Nat`).
-/
instance finite_biUnion'' {ι : Type*} (p : ι → Prop) [h : Finite { x | p x }] (t : ι → Set α)
    [∀ i, Finite (t i)] : Finite (⋃ (x) (_ : p x), t x) :=
  @Finite.Set.finite_biUnion' _ _ (Set.ofPred p) h t _
/-
**Finite.Set.finite_iInter** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_iInter {ι : Sort*} [Nonempty ι] (t : ι -> Set α) [forall i, Finite 
(t i)] : Finite (⋂ i, t i)
参数：t : ι -> Set α；t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.Set.subset`：∀ {α : Type u} (s : Set α) {t : Set α} [Finite ↑s], t
 ⊆ s → Finite ↑t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
instance finite_iInter {ι : Sort*} [Nonempty ι] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋂ i, t i) :=
  Finite.Set.subset (t <| Classical.arbitrary ι) (iInter_subset _ _)

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

/-
**Set.finite_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall i, (f i).Finite) : (
⋃ i, f i).Finite
参数：H : forall i, (f i).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
-/
theorem finite_iUnion [Finite ι] {f : ι → Set α} (H : ∀ i, (f i).Finite) : (⋃ i, f i).Finite :=
  haveI := fun i => (H i).to_subtype
  toFinite _

/-- Dependent version of `Finite.biUnion`. -/
/-
**Set.Finite.biUnion'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {ι : Type u_1} {s : Set ι},   s.Finite →     ∀ {t : (i : ι)
 → i ∈ s → Set α}, (∀ (i : ι) (hi : i ∈ s), (t i hi).Finite) → (⋃ i, ⋃ (h : i ∈ 
s), t i h).Finite
参数：i : ι；∀ (i : ι) (hi : i ∈ s), (t i hi).Finite；⋃ i, ⋃ (h : i ∈ s), t i h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite

--- 原说明 ---
Dependent version of `Finite.biUnion`.
-/
theorem Finite.biUnion' {ι} {s : Set ι} (hs : s.Finite) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i (hi : i ∈ s), (t i hi).Finite) : (⋃ i ∈ s, t i ‹_›).Finite := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]
  apply finite_iUnion fun i : s => ht i.1 i.2
/-
**Set.Finite.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite → ∀ {t : ι → Set α}, (
∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
参数：∀ i ∈ s, (t i).Finite；⋃ i ∈ s, t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.biUnion'`：∀ {α : Type u} {ι : Type u_1} {s : Set ι},   s.Fini
te →     ∀ {t : (i : ι) → i ∈ s → Set α}, (∀ (i : ι) (hi : i ∈ s), (t i hi).Fini
te) → (⋃ …
-/
theorem Finite.biUnion {ι} {s : Set ι} (hs : s.Finite) {t : ι → Set α}
    (ht : ∀ i ∈ s, (t i).Finite) : (⋃ i ∈ s, t i).Finite :=
  hs.biUnion' ht
/-
**Set.Finite.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set (Set α)}, s.Finite → (∀ t ∈ s, t.Finite) → (⋃₀ s).
Finite
参数：Set α；∀ t ∈ s, t.Finite；⋃₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
-/
theorem Finite.sUnion {s : Set (Set α)} (hs : s.Finite) (H : ∀ t ∈ s, Set.Finite t) :
    (⋃₀ s).Finite := by
  simpa only [sUnion_eq_biUnion] using hs.biUnion H
/-
**Set.Finite.sInter** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} {s : Set (Set α)} {t : Set α}, t ∈ s → t.Finite → (⋂₀ s).
Finite
参数：Set α；⋂₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
-/
theorem Finite.sInter {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Finite) :
    (⋂₀ s).Finite :=
  hf.subset (sInter_subset_of_mem ht)

/-- If sets `s i` are finite for all `i` from a finite set `t` and are empty for `i ∉ t`, then the
union `⋃ i, s i` is a finite set. -/
/-
**Set.Finite.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {ι : Type u_1} {s : ι → Set α} {t : Set ι},   t.Finite → (∀
 i ∈ t, (s i).Finite) → (∀ i ∉ t, s i = ∅) → (⋃ i, s i).Finite
参数：∀ i ∈ t, (s i).Finite；∀ i ∉ t, s i = ∅；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite

--- 原说明 ---
If sets `s i` are finite for all `i` from a finite set `t` and are empty for `i 
∉ t`, then the
union `⋃ i, s i` is a finite set.
-/
theorem Finite.iUnion {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Finite)
    (hs : ∀ i ∈ t, (s i).Finite) (he : ∀ i, i ∉ t → s i = ∅) : (⋃ i, s i).Finite := by
  suffices ⋃ i, s i ⊆ ⋃ i ∈ t, s i by exact (ht.biUnion hs).subset this
  refine iUnion_subset fun i x hx => ?_
  by_cases hi : i ∈ t
  · exact mem_biUnion hi hx
  · rw [he i hi, mem_empty_iff_false] at hx
    contradiction

/-- An indexed union of pairwise disjoint sets is finite iff all sets are finite, and all but
finitely many are empty. -/
/-
**Set.finite_iUnion_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：finite_iUnion_iff {ι : Type*} {s : ι -> Set α} (hs : Pairwise fun i j => D
isjoint (s i) (s j)) : (⋃ i, s i).Finite ↔ (forall i, (s i).Finite) ∧ {i | (s i)
.Nonempty}.Finite where mp h
参数：hs : Pairwise fun i j => Disjoint (s i) (s j)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, Pairwise r →
 ¬r a b → a = b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Set.Finite.iUnion`：∀ {α : Type u} {ι : Type u_1} {s : ι → Set α} {t : Se
t ι},   t.Finite → (∀ i ∈ t, (s i).Finite) → (∀ i ∉ t, s i = ∅) → (⋃ i, s i).Fin
ite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
An indexed union of pairwise disjoint sets is finite iff all sets are finite, an
d all but
finitely many are empty.
-/
lemma finite_iUnion_iff {ι : Type*} {s : ι → Set α} (hs : Pairwise fun i j ↦ Disjoint (s i) (s j)) :
    (⋃ i, s i).Finite ↔ (∀ i, (s i).Finite) ∧ {i | (s i).Nonempty}.Finite where
  mp h := by
    refine ⟨fun i ↦ h.subset <| subset_iUnion _ _, ?_⟩
    let u (i : {i | (s i).Nonempty}) : ⋃ i, s i := ⟨i.2.choose, mem_iUnion.2 ⟨i.1, i.2.choose_spec⟩⟩
    have u_inj : Function.Injective u := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      ext
      refine hs.eq <| not_disjoint_iff.2 ⟨u ⟨i, hi⟩, hi.choose_spec, ?_⟩
      rw [hij]
      exact hj.choose_spec
    have : Finite (⋃ i, s i) := h
    exact .of_injective u u_inj
  mpr h := h.2.iUnion (fun _ _ ↦ h.1 _) (by simp [not_nonempty_iff_eq_empty])
/-
**Set.Infinite.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {s : ι → Set α} (i : ι), (s i).Infinite → (⋃
 i, s i).Infinite
参数：i : ι；s i；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
protected lemma Infinite.iUnion {ι : Sort*} {s : ι → Set α} (i : ι) (hi : (s i).Infinite) :
    (⋃ i, s i).Infinite :=
  fun h ↦ hi (h.subset (Set.subset_iUnion s i))
/-
**Set.Infinite.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {s : ι → Set α} (i : ι), (s i).Infinite → (⋃
 i, s i).Infinite
参数：i : ι；s i；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
lemma Infinite.iUnion₂ {ι : Sort*} {κ : ι → Sort*} {s : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (hij : (s i j).Infinite) : (⋃ (i) (j), s i j).Infinite :=
  fun hc ↦ hij (hc.subset <| subset_iUnion₂ _ _)
/-
**Set.finite_iUnion_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} [Subsingleton ι] {s : ι → Set α}, (⋃ i, s i)
.Finite ↔ ∀ (i : ι), (s i).Finite
参数：⋃ i, s i；i : ι；s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_plift_down`：iUnion_plift_down (f : ι -> Set α) : ⋃ i, f (PLif
t.down i) = ⋃ i, f i
· 使用引理 `Set.finite_iUnion_iff`：finite_iUnion_iff {ι : Type*} {s : ι -> Set α} (h
s : Pairwise fun i j => Disjoint (s i) (s j)) : (⋃ i, s i).Finite ↔ (forall i, (
s i).Finite…
· 使用定理 `Subsingleton.pairwise`：∀ {α : Type u_1} {r : α → α → Prop} [Subsingleton
 α], Pairwise r
· 使用定理 `instSubsingletonPLift`：∀ {α : Sort u_1} [Subsingleton α], Subsingleton (
PLift α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma finite_iUnion_of_subsingleton {ι : Sort*} [Subsingleton ι] {s : ι → Set α} :
    (⋃ i, s i).Finite ↔ ∀ i, (s i).Finite := by
  rw [← iUnion_plift_down, finite_iUnion_iff _root_.Subsingleton.pairwise]
  simp [PLift.forall, Finite.of_subsingleton]

/-- An indexed union of pairwise disjoint sets is finite iff all sets are finite, and all but
finitely many are empty. -/
/-
**Set.PairwiseDisjoint.finite_biUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Pairwis
eDisjoint`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : β → Set α} {s : Set β},   s.PairwiseDisjo
int f → ((⋃ i ∈ s, f i).Finite ↔ (∀ i ∈ s, (f i).Finite) ∧ {i | i ∈ s ∧ (f i).No
nempty}.Finite)
参数：(⋃ i ∈ s, f i).Finite ↔ (∀ i ∈ s, (f i).Finite) ∧ {i | i ∈ s ∧ (f i).Nonempty
}.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.finite_iUnion_iff`：finite_iUnion_iff {ι : Type*} {s : ι -> Set α} (h
s : Pairwise fun i j => Disjoint (s i) (s j)) : (⋃ i, s i).Finite ↔ (forall i, (
s i).Finite…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An indexed union of pairwise disjoint sets is finite iff all sets are finite, an
d all but
finitely many are empty.
-/
lemma PairwiseDisjoint.finite_biUnion_iff {f : β → Set α} {s : Set β} (hs : s.PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).Finite ↔ (∀ i ∈ s, (f i).Finite) ∧ {i ∈ s | (f i).Nonempty}.Finite := by
  rw [finite_iUnion_iff (by aesop (add unfold safe [Pairwise, PairwiseDisjoint, Set.Pairwise]))]
  simp

section preimage
variable {f : α → β} {s : Set β}

/-
**Set.Finite.preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}, s.Finite → (∀ b ∈ s, 
(f ⁻¹' {b}).Finite) → (f ⁻¹' s).Finite
参数：∀ b ∈ s, (f ⁻¹' {b}).Finite；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
-/
theorem Finite.preimage' (h : s.Finite) (hf : ∀ b ∈ s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  exact Set.Finite.biUnion h hf

end preimage

/-- A finite union of finsets is finite. -/
/-
**Set.union_finset_finite_of_range_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_finset_finite_of_range_finite (f : α -> Finset β) (h : (range f).Fin
ite) : (⋃ a, (f a : Set β)).Finite
参数：f : α -> Finset β；h : (range f).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
A finite union of finsets is finite.
-/
theorem union_finset_finite_of_range_finite (f : α → Finset β) (h : (range f).Finite) :
    (⋃ a, (f a : Set β)).Finite := by
  rw [← biUnion_range]
  exact h.biUnion fun y _ => y.finite_toSet

end SetFiniteConstructors

/--
If the image of `s` under `f` is finite, and each fiber of `f` has a finite intersection
with `s`, then `s` is itself finite.

It is useful to give `f` explicitly here so this can be used with `apply`.
-/
/-
**Set.Finite.of_finite_fibers** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) {s : Set α}, (f '' s).Finite → (∀ 
x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite) → s.Finite
参数：f : α → β；f '' s；∀ x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
If the image of `s` under `f` is finite, and each fiber of `f` has a finite inte
rsection
with `s`, then `s` is itself finite.

It is useful to give `f` explicitly here so this can be used with `apply`.
-/
lemma Finite.of_finite_fibers (f : α → β) {s : Set α} (himage : (f '' s).Finite)
    (hfibers : ∀ x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite) : s.Finite :=
  (himage.biUnion hfibers).subset fun x ↦ by aesop

/-! ### Properties -/

/-
**Set.finite_subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_subset_iUnion {s : Set α} (hs : s.Finite) {ι} {t : ι -> Set α} (h :
 s subseteq ⋃ i, t i) : exists I : Set ι, I.Finite ∧ s subseteq ⋃ i in I, t i
参数：hs : s.Finite；h : s subseteq ⋃ i, t i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
### Properties
-/
theorem finite_subset_iUnion {s : Set α} (hs : s.Finite) {ι} {t : ι → Set α} (h : s ⊆ ⋃ i, t i) :
    ∃ I : Set ι, I.Finite ∧ s ⊆ ⋃ i ∈ I, t i := by
  have := hs.to_subtype
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i by simpa [subset_def] using h
  refine ⟨range f, finite_range f, fun x hx => ?_⟩
  rw [biUnion_range, mem_iUnion]
  exact ⟨⟨x, hx⟩, hf _⟩
/-
**Set.eq_finite_iUnion_of_finite_subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_finite_iUnion_of_finite_subset_iUnion {ι} {s : ι -> Set α} {t : Set α} 
(tfin : t.Finite) (h : t subseteq ⋃ i, s i) : exists I : Set ι, I.Finite ∧ exist
s σ : { i | i in I } -> Set α, (forall i, (σ i).Finite) ∧ (forall i, σ i subsete
q s i) ∧ t = ⋃ i, σ i
参数：tfin : t.Finite；h : t subseteq ⋃ i, s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_subset_iUnion`：finite_subset_iUnion {s : Set α} (hs : s.Finit
e) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i) : exists I : Set ι, I.Finite ∧
 s subseteq ⋃ …
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem eq_finite_iUnion_of_finite_subset_iUnion {ι} {s : ι → Set α} {t : Set α} (tfin : t.Finite)
    (h : t ⊆ ⋃ i, s i) :
    ∃ I : Set ι,
      I.Finite ∧
        ∃ σ : { i | i ∈ I } → Set α, (∀ i, (σ i).Finite) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_iUnion tfin h
  ⟨I, Ifin, fun x => s x ∩ t, fun _ => tfin.subset inter_subset_right, fun _ =>
    inter_subset_left, by
    ext x
    rw [mem_iUnion]
    constructor
    · intro x_in
      rcases mem_iUnion.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      exact ⟨⟨i, hi⟩, ⟨H, x_in⟩⟩
    · rintro ⟨i, -, H⟩
      exact H⟩

/-! ### Infinite sets -/

variable {s t : Set α}

/-
**Set.infinite_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_iUnion {ι : Type*} [Infinite ι] {s : ι -> Set α} (hs : Function.I
njective s) : (⋃ i, s i).Infinite
参数：hs : Function.Injective s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.Finite.finite_subsets`：∀ {α : Type u} {a : Set α}, a.Finite → {b | b
 ⊆ a}.Finite
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem infinite_iUnion {ι : Type*} [Infinite ι] {s : ι → Set α} (hs : Function.Injective s) :
    (⋃ i, s i).Infinite :=
  fun hfin ↦ @not_injective_infinite_finite ι _ _ hfin.finite_subsets.to_subtype
    (fun i ↦ ⟨s i, subset_iUnion _ _⟩) fun _ _ h_eq ↦ hs (Subtype.ext_iff.1 h_eq)
/-
**Set.Infinite.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {ι : Type u_1} {s : ι → Set α} {a : Set ι}, a.Infinite → Se
t.InjOn s a → (⋃ i ∈ a, s i).Infinite
参数：⋃ i ∈ a, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.infinite_iUnion`：infinite_iUnion {ι : Type*} [Infinite ι] {s : ι -> 
Set α} (hs : Function.Injective s) : (⋃ i, s i).Infinite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Infinite.biUnion {ι : Type*} {s : ι → Set α} {a : Set ι} (ha : a.Infinite)
    (hs : a.InjOn s) : (⋃ i ∈ a, s i).Infinite := by
  rw [biUnion_eq_iUnion]
  have _ := ha.to_subtype
  exact infinite_iUnion fun ⟨i,hi⟩ ⟨j,hj⟩ hij ↦ by simp [hs hi hj hij]
/-
**Set.Infinite.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s : Set (Set α)}, s.Infinite → (⋃₀ s).Infinite
参数：Set α；⋃₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.infinite_iUnion`：infinite_iUnion {ι : Type*} [Infinite ι] {s : ι -> 
Set α} (hs : Function.Injective s) : (⋃ i, s i).Infinite
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem Infinite.sUnion {s : Set (Set α)} (hs : s.Infinite) : (⋃₀ s).Infinite := by
  rw [sUnion_eq_iUnion]
  have _ := hs.to_subtype
  exact infinite_iUnion Subtype.coe_injective

/-! ### Order properties -/

@[to_dual]
/-
**Set.map_finite_biSup** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：map_finite_biSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [Fu
nLike F α β] [SupBotHomClass F α β] {s : Set ι} (hs : s.Finite) (f : F) (g : ι -
> α) : f (⨆ x in s, g x) = ⨆ x in s, f (g x)
参数：hs : s.Finite；f : F；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s

--- 原说明 ---
### Order properties
-/
lemma map_finite_biSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] {s : Set ι} (hs : s.Finite) (f : F) (g : ι → α) :
    f (⨆ x ∈ s, g x) = ⨆ x ∈ s, f (g x) := by
  have := map_finset_sup f hs.toFinset g
  simp only [Finset.sup_eq_iSup, hs.mem_toFinset, comp_apply] at this
  exact this

@[to_dual]
/-
**Set.map_finite_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：map_finite_iSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [Fun
Like F α β] [SupBotHomClass F α β] [Finite ι] (f : F) (g : ι -> α) : f (⨆ i, g i
) = ⨆ i, f (g i)
参数：f : F；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
· 使用引理 `Set.map_finite_biSup`：map_finite_biSup {F ι : Type*} [CompleteLattice α]
 [CompleteLattice β] [FunLike F α β] [SupBotHomClass F α β] {s : Set ι} (hs : s.
Finite) (f…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma map_finite_iSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] [Finite ι] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [← iSup_univ (f := g), ← iSup_univ (f := fun i ↦ f (g i))]
  exact map_finite_biSup finite_univ f g

@[to_dual]
/-
**Set.Finite.iSup_biInf_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [inst : Preorder ι'] [None
mpty ι'] [IsDirectedOrder ι']   [inst_3 : Order.Frame α] {s : Set ι},   s.Finite
 → ∀ {f : ι → ι' → α}, (∀ i ∈ s, Monotone (f i)) → ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s
, ⨆ j, f i j
参数：∀ i ∈ s, Monotone (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iInf_insert`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{f : β → α} {s : Set β} {b : β},   ⨅ x ∈ insert b s, f x = f b ⊓ ⨅ x ∈ s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.forall_mem_insert`：forall_mem_insert {P : α -> Prop} {a : α} {s : Se
t α} : (forall x in insert a s, P x) ↔ P a ∧ forall x in s, P x
· 使用定理 `iSup_inf_of_monotone`：∀ {α : Type u} [inst : Order.Frame α] {ι : Type u_
1} [inst_1 : Preorder ι] [IsDirectedOrder ι] {f g : ι → α},   Monotone f → Monot
one g → ⨆ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
-/
theorem Finite.iSup_biInf_of_monotone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirectedOrder ι'] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s, ⨆ j, f i j := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [iSup_const]
  | insert _ _ ihs =>
    rw [forall_mem_insert] at hf
    simp only [iInf_insert, ← ihs hf.2]
    exact iSup_inf_of_monotone hf.1 fun j₁ j₂ hj => iInf₂_mono fun i hi => hf.2 i hi hj

@[to_dual]
/-
**Set.Finite.iSup_biInf_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [inst : Preorder ι'] [None
mpty ι'] [IsCodirectedOrder ι']   [inst_3 : Order.Frame α] {s : Set ι},   s.Fini
te → ∀ {f : ι → ι' → α}, (∀ i ∈ s, Antitone (f i)) → ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈
 s, ⨆ j, f i j
参数：∀ i ∈ s, Antitone (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.iSup_biInf_of_monotone`：∀ {ι : Type u_1} {ι' : Type u_2} {α :
 Type u_3} [inst : Preorder ι'] [Nonempty ι'] [IsDirectedOrder ι']   [inst_3 : O
rder.Frame α] {s : Set …
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem Finite.iSup_biInf_of_antitone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsCodirectedOrder ι'] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s, ⨆ j, f i j :=
  @Finite.iSup_biInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left

@[to_dual]
/-
**Set._root_.iSup_iInf_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.iSup_iInf_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirectedOrder ι'] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j := by
  simpa only [iInf_univ] using finite_univ.iSup_biInf_of_monotone fun i _ => hf i

@[to_dual]
/-
**Set._root_.iSup_iInf_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.iSup_iInf_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsCodirectedOrder ι'] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j :=
  @iSup_iInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left

@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_monotone := iSup_iInf_of_monotone
@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_antitone := iSup_iInf_of_antitone
@[deprecated (since := "2026-02-03")] protected alias iInf_iSup_of_monotone := iInf_iSup_of_monotone
@[deprecated (since := "2026-02-03")] protected alias iInf_iSup_of_antitone := iInf_iSup_of_antitone

/-- An increasing union distributes over finite intersection. -/
/-
**Set.iUnion_iInter_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iInter_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDir
ectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Monotone (s 
i)) : ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j
参数：hs : forall i, Monotone (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iInf_of_monotone`：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [
Finite ι] [inst : Preorder ι'] [Nonempty ι'] [IsDirectedOrder ι']   [inst_3 : Or
der.Frame α…

--- 原说明 ---
An increasing union distributes over finite intersection.
-/
theorem iUnion_iInter_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_monotone hs

/-- A decreasing union distributes over finite intersection. -/
/-
**Set.iUnion_iInter_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_iInter_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsCod
irectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Antitone (
s i)) : ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j
参数：hs : forall i, Antitone (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_iInf_of_antitone`：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [
Finite ι] [inst : Preorder ι'] [Nonempty ι'] [IsCodirectedOrder ι']   [inst_3 : 
Order.Frame…

--- 原说明 ---
A decreasing union distributes over finite intersection.
-/
theorem iUnion_iInter_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsCodirectedOrder ι'] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_antitone hs

/-- An increasing intersection distributes over finite union. -/
/-
**Set.iInter_iUnion_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_iUnion_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsCod
irectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Monotone (
s i)) : ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j
参数：hs : forall i, Monotone (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_iSup_of_monotone`：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [
Finite ι] [inst : Preorder ι'] [Nonempty ι'] [IsCodirectedOrder ι']   [inst_3 : 
Order.Cofra…

--- 原说明 ---
An increasing intersection distributes over finite union.
-/
theorem iInter_iUnion_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsCodirectedOrder ι'] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_monotone hs

/-- A decreasing intersection distributes over finite union. -/
/-
**Set.iInter_iUnion_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_iUnion_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDir
ectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Antitone (s 
i)) : ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j
参数：hs : forall i, Antitone (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_iSup_of_antitone`：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [
Finite ι] [inst : Preorder ι'] [Nonempty ι'] [IsDirectedOrder ι']   [inst_3 : Or
der.Coframe…

--- 原说明 ---
A decreasing intersection distributes over finite union.
-/
theorem iInter_iUnion_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_antitone hs
/-
**Set.iUnion_pi_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] {α : ι
 -> Type*} {I : Set ι} {s : forall i, ι' -> Set (α i)} (hI : I.Finite) (hs : for
all i in I, Monotone (s i)) : ⋃ j : ι', I.pi (fun i => s i j) = I.pi fun i => ⋃ 
j, s i j
参数：α i；hI : I.Finite；hs : forall i in I, Monotone (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
· 使用定理 `Set.iUnion_iInter_of_monotone`：iUnion_iInter_of_monotone {ι ι' α : Type*
} [Finite ι] [Preorder ι'] [IsDirectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Se
t α} (hs : forall i…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem iUnion_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] {α : ι → Type*}
    {I : Set ι} {s : ∀ i, ι' → Set (α i)} (hI : I.Finite) (hs : ∀ i ∈ I, Monotone (s i)) :
    ⋃ j : ι', I.pi (fun i => s i j) = I.pi fun i => ⋃ j, s i j := by
  simp only [pi_def, biInter_eq_iInter, preimage_iUnion]
  have := hI.fintype.finite
  refine iUnion_iInter_of_monotone (ι' := ι') (fun (i : I) j₁ j₂ h => ?_)
  exact preimage_mono <| hs i i.2 h
/-
**Set.iUnion_univ_pi_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_univ_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] [
Finite ι] {α : ι -> Type*} {s : forall i, ι' -> Set (α i)} (hs : forall i, Monot
one (s i)) : ⋃ j : ι', pi univ (fun i => s i j) = pi univ fun i => ⋃ j, s i j
参数：α i；hs : forall i, Monotone (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_pi_of_monotone`：iUnion_pi_of_monotone {ι ι' : Type*} [LinearO
rder ι'] [Nonempty ι'] {α : ι -> Type*} {I : Set ι} {s : forall i, ι' -> Set (α 
i)} (hI : I.Fin…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
theorem iUnion_univ_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
    {α : ι → Type*} {s : ∀ i, ι' → Set (α i)} (hs : ∀ i, Monotone (s i)) :
    ⋃ j : ι', pi univ (fun i => s i j) = pi univ fun i => ⋃ j, s i j :=
  iUnion_pi_of_monotone finite_univ fun i _ => hs i
/-
**Set._root_.iInf_iSup_eq_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.iInf_iSup_eq_of_finite {ι : Sort v} {κ : ι → Sort w} [Order.Frame α] [Finite ι]
    {f : Π a, κ a → α} : ⨅ a, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a, f a (g a) := by
  suffices ∀ {ι : Type v} {κ : ι → Type w} [Finite ι] (f : Π a, κ a → α),
      ⨅ a, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a, f a (g a) by
    simpa [← Equiv.plift.symm.iInf_comp, ← Equiv.plift.symm.iSup_comp,
        ← (Equiv.plift.piCongr fun a => @Equiv.plift (κ a.down)).symm.iSup_comp] using!
      this (κ := fun a => PLift (κ a.down)) fun (a : PLift ι) b => f a.down b.down
  intro ι κ _ f
  induction ι using Finite.induction_empty_option with
  | of_equiv e h => simp [← e.iInf_comp, ← e.piCongrLeft κ |>.iSup_comp, h]
  | h_empty => simp [iInf_of_empty, iSup_const]
  | h_option h =>
    simp only [iInf_option, h, ← (Equiv.piOptionEquivProd (β := κ)).symm.iSup_comp,
      Equiv.piOptionEquivProd_symm_apply, iSup_prod, ← inf_iSup_eq, ← iSup_inf_eq]
/-
**Set._root_.iSup_iInf_eq_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.iSup_iInf_eq_of_finite {ι : Sort v} {κ : ι → Sort w} [Order.Coframe α] [Finite ι]
    {f : ∀ a, κ a → α} : ⨆ a, ⨅ b, f a b = ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  iInf_iSup_eq_of_finite (α := αᵒᵈ)
/-
**Set.Finite.biInf_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {ι : Type v} {κ : ι → Sort w} [Nonempty ((a : ι) → κ a)] [i
nst : Order.Frame α] {s : Set ι},   s.Finite → ∀ {f : (a : ι) → κ a → α}, ⨅ a ∈ 
s, ⨆ b, f a b = ⨆ g, ⨅ a ∈ s, f a (g a)
参数：(a : ι) → κ a；a : ι；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_iSup_eq_of_finite`：∀ {α : Type u} {ι : Sort v} {κ : ι → Sort w} [in
st : Order.Frame α] [Finite ι] {f : (a : ι) → κ a → α},   ⨅ a, ⨆ b, f a b = ⨆ g,
 ⨅ a, f a (g…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `Equiv.piEquivPiSubtypeProd_symm_apply`：∀ {α : Type u_9} (p : α → Prop) (
β : α → Type u_10) [inst : DecidablePred p]   (f : ((i : { x // p x }) → β ↑i) ×
 ((i : { x // ¬p x }) → β ↑…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
· 使用定理 `iSup_const`：iSup_const [Nonempty ι] : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.nonempty`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Nonempty β], No
nempty α
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.plift_symm_apply`：∀ {α : Sort u}, ⇑Equiv.plift.symm = PLift.up
· 使用定理 `Equiv.piCongrRight_symm_apply`：∀ {α : Sort u_1} {β₁ : α → Sort u_9} {β₂ 
: α → Sort u_10} (F : (a : α) → β₁ a ≃ β₂ a) (a : (i : α) → β₂ i) (i : α),   (Eq
uiv.piCongrRight F)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Finite.biInf_iSup_eq {ι : Type v} {κ : ι → Sort w} [Nonempty (Π a, κ a)] [Order.Frame α]
    {s : Set ι} (hs : s.Finite) {f : Π a, κ a → α} :
    ⨅ a ∈ s, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a ∈ s, f a (g a) := by
  classical
  suffices h : ∀ {κ : ι → Type w} [Nonempty (Π a, κ a)] (f : Π a, κ a → α),
      ⨅ a ∈ s, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a ∈ s, f a (g a) by
    have : Nonempty (Π a, PLift (κ a)) := (Equiv.piCongrRight fun _ => Equiv.plift).nonempty
    simpa [← Equiv.plift.symm.iSup_comp, ← (Equiv.piCongrRight fun _ => Equiv.plift).symm.iSup_comp]
      using h (κ := fun a => PLift (κ a)) fun a b => f a b.down
  intro κ _ f
  have := hs.to_subtype
  have : Nonempty (Π a : { a // a ∉ s }, κ ↑a) := ‹Nonempty (Π a, κ a)›.map fun f a ↦ f a
  simp [← iInf_subtype'', iInf_iSup_eq_of_finite (ι := s),
    ← Equiv.piEquivPiSubtypeProd (· ∈ s) _ |>.symm.iSup_comp, iSup_prod, iSup_const]
/-
**Set.Finite.biSup_iInf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {ι : Type v} {κ : ι → Sort w} [Nonempty ((a : ι) → κ a)] [i
nst : Order.Coframe α] {s : Set ι},   s.Finite → ∀ {f : (a : ι) → κ a → α}, ⨆ a 
∈ s, ⨅ b, f a b = ⨅ g, ⨆ a ∈ s, f a (g a)
参数：(a : ι) → κ a；a : ι；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.biInf_iSup_eq`：∀ {α : Type u} {ι : Type v} {κ : ι → Sort w} [
Nonempty ((a : ι) → κ a)] [inst : Order.Frame α] {s : Set ι},   s.Finite → ∀ {f 
: (a : ι) → κ …
-/
theorem Finite.biSup_iInf_eq {ι : Type v} {κ : ι → Sort w} [Nonempty (∀ a, κ a)] [Order.Coframe α]
    {s : Set ι} (hs : s.Finite) {f : ∀ a, κ a → α} :
    ⨆ a ∈ s, ⨅ b, f a b = ⨅ g : ∀ a, κ a, ⨆ a ∈ s, f a (g a) :=
  hs.biInf_iSup_eq (α := αᵒᵈ)

section

variable [Preorder α] [IsDirectedOrder α] [Nonempty α] {s : Set α}

/-- A finite set is bounded above. -/
@[to_dual /-- A finite set is bounded below. -/]
/-
**Set.Finite.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder α] [Nonempty α] {s : S
et α}, s.Finite → BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `bddAbove_empty`：bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α)
· 使用定理 `BddAbove.insert`：∀ {α : Type u_1} [inst : Preorder α] [IsDirectedOrder α
] {s : Set α} (a : α), BddAbove s → BddAbove (insert a s)

--- 原说明 ---
A finite set is bounded above.
-/
protected theorem Finite.bddAbove (hs : s.Finite) : BddAbove s :=
  Finite.induction_on _ hs bddAbove_empty fun _ _ h => h.insert _

/-- A finite union of sets which are all bounded above is still bounded above. -/
@[to_dual /-- A finite union of sets which are all bounded below is still bounded below. -/]
/-
**Set.Finite.bddAbove_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [IsDirectedOrder α] [Nonem
pty α] {I : Set β} {S : β → Set α},   I.Finite → (BddAbove (⋃ i ∈ I, S i) ↔ ∀ i 
∈ I, BddAbove (S i))
参数：BddAbove (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddAbove (S i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_empty`：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), 
s x = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x

--- 原说明 ---
A finite union of sets which are all bounded above is still bounded above.
-/
theorem Finite.bddAbove_biUnion {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddAbove (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddAbove (S i) := by
  induction I, H using Set.Finite.induction_on with
  | empty => simp only [biUnion_empty, bddAbove_empty, forall_mem_empty]
  | insert _ _ hs => simp only [biUnion_insert, forall_mem_insert, bddAbove_union, hs]

@[to_dual]
/-
**Set.infinite_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_of_not_bddAbove : ¬BddAbove s -> s.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
-/
theorem infinite_of_not_bddAbove : ¬BddAbove s → s.Infinite :=
  mt Finite.bddAbove

end

end Set

/-- A finset is bounded above. -/
@[to_dual /-- A finset is bounded below. -/]
/-
**Finset.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u} [inst : SemilatticeSup α] [Nonempty α] (s : Finset α), BddA
bove ↑s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
A finset is bounded above.
-/
protected theorem Finset.bddAbove [SemilatticeSup α] [Nonempty α] (s : Finset α) :
    BddAbove (↑s : Set α) :=
  s.finite_toSet.bddAbove

section LinearOrder
variable [LinearOrder α] {s : Set α}

/-
**Set.finite_sdiff_iUnion_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.finite_sdiff_iUnion_Ioo (s : Set α) : (s \ ⋃ (x in s) (y in s), Ioo x 
y).Finite
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.finite_of_forall_not_lt_lt`：Set.finite_of_forall_not_lt_lt (h : fora
ll x in s, forall y in s, forall z in s, x < y -> y < z -> False) : Set.Finite s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Set.finite_sdiff_iUnion_Ioo (s : Set α) : (s \ ⋃ (x ∈ s) (y ∈ s), Ioo x y).Finite :=
  Set.finite_of_forall_not_lt_lt fun _x hx _y hy _z hz hxy hyz => hy.2 <| mem_iUnion₂_of_mem hx.1 <|
    mem_iUnion₂_of_mem hz.1 ⟨hxy, hyz⟩

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo := Set.finite_sdiff_iUnion_Ioo
/-
**Set.finite_sdiff_iUnion_Ioo'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.finite_sdiff_iUnion_Ioo' (s : Set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).
Finite
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.finite_sdiff_iUnion_Ioo`：Set.finite_sdiff_iUnion_Ioo (s : Set α) : (
s \ ⋃ (x in s) (y in s), Ioo x y).Finite
-/
lemma Set.finite_sdiff_iUnion_Ioo' (s : Set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite := by
  simpa only [iUnion, iSup_prod, iSup_subtype] using s.finite_sdiff_iUnion_Ioo

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo' := Set.finite_sdiff_iUnion_Ioo'
/-
**Directed.exists_mem_subset_of_finset_subset_biUnion** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：Directed.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempt
y ι] {f : ι -> Set α} (h : Directed (· subseteq ·) f) {s : Finset α} (hs : (s : 
Set α) subseteq ⋃ i, f i) : exists i, (s : Set α) subseteq f i
参数：h : Directed (· subseteq ·) f；hs : (s : Set α) subseteq ⋃ i, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma Directed.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempty ι]
    {f : ι → Set α} (h : Directed (· ⊆ ·) f) {s : Finset α} (hs : (s : Set α) ⊆ ⋃ i, f i) :
    ∃ i, (s : Set α) ⊆ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons b t hbt iht =>
    simp only [Finset.coe_cons, Set.insert_subset_iff, Set.mem_iUnion] at hs ⊢
    rcases hs.imp_right iht with ⟨⟨i, hi⟩, j, hj⟩
    rcases h i j with ⟨k, hik, hjk⟩
    exact ⟨k, hik hi, hj.trans hjk⟩
/-
**DirectedOn.exists_mem_subset_of_finset_subset_biUnion** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：DirectedOn.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι
 -> Set α} {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i subset
eq f j) c) {s : Finset α} (hs : (s : Set α) subseteq ⋃ i in c, f i) : exists i i
n c, (s : Set α) subseteq f i
参数：hn : c.Nonempty；hc : DirectedOn (fun i j => f i subseteq f j) c；hs : (s : Set
 α) subseteq ⋃ i in c, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty
 ↑s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Directed.exists_mem_subset_of_finset_subset_biUnion`：Directed.exists_mem
_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempty ι] {f : ι -> Set α} (h 
: Directed (· subseteq ·) f) {s : Finset …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directed_comp`：directed_comp {ι} {f : ι -> β} {g : β -> α} : Directed r 
(g ∘ f) ↔ Directed (g ⁻¹'o r) f
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
-/
theorem DirectedOn.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι → Set α}
    {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α}
    (hs : (s : Set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : Set α) ⊆ f i := by
  rw [Set.biUnion_eq_iUnion] at hs
  have := hn.coe_sort
  simpa using (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs
/-
**DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion {α : Type*} {c : S
et (Set α)} (hn : c.Nonempty) (hc : DirectedOn (· subseteq ·) c) {s : Set α} (hs
 : s.Finite) (hsc : s subseteq sUnion c) : exists t in c, s subseteq t
参数：Set α；hn : c.Nonempty；hc : DirectedOn (· subseteq ·) c；hs : s.Finite；hsc : s 
subseteq sUnion c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.exists_mem_subset_of_finset_subset_biUnion`：DirectedOn.exists
_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι -> Set α} {c : Set ι} 
(hn : c.Nonempty) (hc : DirectedOn (fun i j…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion {α : Type*} {c : Set (Set α)}
    (hn : c.Nonempty) (hc : DirectedOn (· ⊆ ·) c) {s : Set α} (hs : s.Finite)
    (hsc : s ⊆ sUnion c) : ∃ t ∈ c, s ⊆ t := by
  rw [← hs.coe_toFinset, sUnion_eq_biUnion] at hsc
  have := DirectedOn.exists_mem_subset_of_finset_subset_biUnion hn hc hsc
  exact hs.coe_toFinset ▸ this

end LinearOrder

