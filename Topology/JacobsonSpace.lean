/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Tactic.CrossRefAttribute

/-!

# Jacobson spaces

## Main results
- `JacobsonSpace`: The class of Jacobson spaces, i.e.
  spaces such that the set of closed points are dense in every closed subspace.
- `jacobsonSpace_iff_locallyClosed`:
  `X` is a Jacobson space iff every locally closed subset contains a closed point of `X`.
- `JacobsonSpace.discreteTopology`:
  If `X` only has finitely many closed points, then the topology on `X` is discrete.

## References
- https://stacks.math.columbia.edu/tag/005T

-/

@[expose] public section

open Topology TopologicalSpace

variable (X) {Y} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

section closedPoints

/-- The set of closed points. -/
/-
**closedPoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：closedPoints : Set X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of closed points.
-/
def closedPoints : Set X := Set.ofPred (IsClosed {·})

variable {X}

@[simp]
/-
**mem_closedPoints_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_closedPoints_iff {x} : x in closedPoints X ↔ IsClosed {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_closedPoints_iff {x} : x ∈ closedPoints X ↔ IsClosed {x} := Iff.rfl
/-
**preimage_closedPoints_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preimage_closedPoints_subset (hf : Function.Injective f) (hf' : Continuous
 f) : f ⁻¹' closedPoints Y subseteq closedPoints X
参数：hf : Function.Injective f；hf' : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_closedPoints_iff`：mem_closedPoints_iff {x} : x in closedPoints X ↔ I
sClosed {x}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
-/
lemma preimage_closedPoints_subset (hf : Function.Injective f) (hf' : Continuous f) :
    f ⁻¹' closedPoints Y ⊆ closedPoints X := by
  intro x hx
  rw [mem_closedPoints_iff]
  convert! continuous_iff_isClosed.mp hf' _ hx
  rw [← Set.image_singleton, Set.preimage_image_eq _ hf]
/-
**Topology.IsClosedEmbedding.preimage_closedPoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.preimage_closedPoints (hf : IsClosedEmbedding f
) : f ⁻¹' closedPoints Y = closedPoints X
参数：hf : IsClosedEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.IsClosedEmbedding.preimage_closedPoints (hf : IsClosedEmbedding f) :
    f ⁻¹' closedPoints Y = closedPoints X := by
  ext x
  simp [mem_closedPoints_iff, ← Set.image_singleton, hf.isClosed_iff_image_isClosed]
/-
**closedPoints_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closedPoints_eq_univ [T1Space X] : closedPoints X = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
lemma closedPoints_eq_univ [T1Space X] :
    closedPoints X = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun _ ↦ isClosed_singleton
/-
**Set.Finite.isDiscrete_of_subset_closedPoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.isDiscrete_of_subset_closedPoints {s : Set X} (hs : s.Finite) (
hs' : s subseteq closedPoints X) : IsDiscrete s
参数：hs : s.Finite；hs' : s subseteq closedPoints X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Set.Finite.isDiscrete_of_subset_closedPoints
    {s : Set X} (hs : s.Finite) (hs' : s ⊆ closedPoints X) : IsDiscrete s := by
  have : T1Space s := ⟨fun x ↦ by convert! (hs' x.2).preimage continuous_subtype_val; aesop⟩
  have : Finite s := hs
  exact ⟨inferInstance⟩

end closedPoints

/-- The class of Jacobson spaces, i.e.
spaces such that the set of closed points are dense in every closed subspace. -/
@[mk_iff, stacks 005U]
/-
**JacobsonSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_1) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of Jacobson spaces, i.e.
spaces such that the set of closed points are dense in every closed subspace.
-/
class JacobsonSpace : Prop where
  closure_inter_closedPoints : ∀ {Z}, IsClosed Z → closure (Z ∩ closedPoints X) = Z

export JacobsonSpace (closure_inter_closedPoints)

variable {X}
/-
**closure_closedPoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_closedPoints [JacobsonSpace X] : closure (closedPoints X) = Set.un
iv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `JacobsonSpace.closure_inter_closedPoints`：∀ {X : Type u_1} {inst : Topol
ogicalSpace X} [self : JacobsonSpace X] {Z : Set X},   IsClosed Z → closure (Z ∩
 closedPoints X) = Z
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
-/
lemma closure_closedPoints [JacobsonSpace X] : closure (closedPoints X) = Set.univ := by
  simpa using closure_inter_closedPoints isClosed_univ
/-
**jacobsonSpace_iff_locallyClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：jacobsonSpace_iff_locallyClosed : JacobsonSpace X ↔ forall Z, Z.Nonempty -
> IsLocallyClosed Z -> (Z inter closedPoints X).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobsonSpace_iff`：∀ (X : Type u_1) [inst : TopologicalSpace X],   Jacob
sonSpace X ↔ ∀ {Z : Set X}, IsClosed Z → closure (Z ∩ closedPoints X) = Z
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.bot_eq_empty`：bot_eq_empty : (⊥ : Set α) = ∅
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用引理 `IsLocallyClosed.inter`：IsLocallyClosed.inter (hs : IsLocallyClosed s) (h
t : IsLocallyClosed t) : IsLocallyClosed (s inter t)
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
lemma jacobsonSpace_iff_locallyClosed :
    JacobsonSpace X ↔ ∀ Z, Z.Nonempty → IsLocallyClosed Z → (Z ∩ closedPoints X).Nonempty := by
  rw [jacobsonSpace_iff]
  constructor
  · simp_rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff,
      Set.nonempty_iff_ne_empty]
    intro H Z hZ hZ' e
    have : Z ⊆ closure Z \ Z := by
      refine subset_closure.trans ?_
      nth_rw 1 [← H isClosed_closure]
      rw [hZ'.closure_subset_iff, Set.subset_sdiff, Set.disjoint_iff, Set.inter_assoc,
        Set.inter_comm _ Z, e]
      exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩
    rw [Set.subset_sdiff, disjoint_self, Set.bot_eq_empty] at this
    exact hZ this.2
  · intro H Z hZ
    refine subset_antisymm (hZ.closure_subset_iff.mpr Set.inter_subset_left) ?_
    rw [← Set.disjoint_compl_left_iff_subset, Set.disjoint_iff_inter_eq_empty,
      ← Set.not_nonempty_iff_eq_empty]
    intro H'
    have := H _ H' (isClosed_closure.isOpen_compl.isLocallyClosed.inter hZ.isLocallyClosed)
    rw [Set.nonempty_iff_ne_empty, Set.inter_assoc, ne_eq,
      ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset] at this
    exact this subset_closure
/-
**nonempty_inter_closedPoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonempty_inter_closedPoints [JacobsonSpace X] {Z : Set X} (hZ : Z.Nonempty
) (hZ' : IsLocallyClosed Z) : (Z inter closedPoints X).Nonempty
参数：hZ : Z.Nonempty；hZ' : IsLocallyClosed Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `jacobsonSpace_iff_locallyClosed`：jacobsonSpace_iff_locallyClosed : Jacob
sonSpace X ↔ forall Z, Z.Nonempty -> IsLocallyClosed Z -> (Z inter closedPoints 
X).Nonempty
-/
lemma nonempty_inter_closedPoints [JacobsonSpace X] {Z : Set X}
    (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z ∩ closedPoints X).Nonempty :=
  jacobsonSpace_iff_locallyClosed.mp inferInstance Z hZ hZ'
/-
**JacobsonSpace.closure_inter_closedPoints_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：JacobsonSpace.closure_inter_closedPoints_eq_closure [JacobsonSpace X] {S :
 Set X} (hS : IsLocallyClosed S) : closure (S inter closedPoints X) = closure S
参数：hS : IsLocallyClosed S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `nonempty_inter_closedPoints`：nonempty_inter_closedPoints [JacobsonSpace 
X] {Z : Set X} (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z inter closedPoin
ts X).Nonempty
· 使用引理 `IsLocallyClosed.inter`：IsLocallyClosed.inter (hs : IsLocallyClosed s) (h
t : IsLocallyClosed t) : IsLocallyClosed (s inter t)
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem JacobsonSpace.closure_inter_closedPoints_eq_closure [JacobsonSpace X]
    {S : Set X} (hS : IsLocallyClosed S) : closure (S ∩ closedPoints X) = closure S := by
  refine (closure_mono (Set.inter_subset_left)).antisymm ?_
  rw [IsClosed.closure_subset_iff isClosed_closure]
  intro x hx
  by_contra H
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := nonempty_inter_closedPoints (Z := S \ closure (S ∩ closedPoints X))
    ⟨x, hx, H⟩ (.inter hS isClosed_closure.isOpen_compl.isLocallyClosed)
  exact hy₂ (subset_closure ⟨hy₁, hy₃⟩)
/-
**isClosed_singleton_of_isLocallyClosed_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_singleton_of_isLocallyClosed_singleton [JacobsonSpace X] {x : X} 
(hx : IsLocallyClosed {x}) : IsClosed {x}
参数：hx : IsLocallyClosed {x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonempty_inter_closedPoints`：nonempty_inter_closedPoints [JacobsonSpace 
X] {Z : Set X} (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z inter closedPoin
ts X).Nonempty
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
-/
lemma isClosed_singleton_of_isLocallyClosed_singleton [JacobsonSpace X] {x : X}
    (hx : IsLocallyClosed {x}) : IsClosed {x} := by
  obtain ⟨_, ⟨y, rfl : y = x, rfl⟩, hy'⟩ :=
    nonempty_inter_closedPoints (Set.singleton_nonempty x) hx
  exact hy'
/-
**Topology.IsOpenEmbedding.preimage_closedPoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.preimage_closedPoints (hf : IsOpenEmbedding f) [J
acobsonSpace Y] : f ⁻¹' closedPoints Y = closedPoints X
参数：hf : IsOpenEmbedding f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `preimage_closedPoints_subset`：preimage_closedPoints_subset (hf : Functio
n.Injective f) (hf' : Continuous f) : f ⁻¹' closedPoints Y subseteq closedPoints
 X
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用引理 `isClosed_singleton_of_isLocallyClosed_singleton`：isClosed_singleton_of_i
sLocallyClosed_singleton [JacobsonSpace X] {x : X} (hx : IsLocallyClosed {x}) : 
IsClosed {x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `IsLocallyClosed.image`：IsLocallyClosed.image {s : Set X} (hs : IsLocally
Closed s) {f : X -> Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) : I
sLocallyClo…
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
lemma Topology.IsOpenEmbedding.preimage_closedPoints (hf : IsOpenEmbedding f) [JacobsonSpace Y] :
    f ⁻¹' closedPoints Y = closedPoints X := by
  apply subset_antisymm (preimage_closedPoints_subset hf.injective hf.continuous)
  intro x hx
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← Set.image_singleton]
  exact (hx.isLocallyClosed.image hf.isInducing hf.isOpen_range.isLocallyClosed)
/-
**JacobsonSpace.of_isOpenEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：JacobsonSpace.of_isOpenEmbedding [JacobsonSpace Y] (hf : IsOpenEmbedding f
) : JacobsonSpace X
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `jacobsonSpace_iff_locallyClosed`：jacobsonSpace_iff_locallyClosed : Jacob
sonSpace X ↔ forall Z, Z.Nonempty -> IsLocallyClosed Z -> (Z inter closedPoints 
X).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsOpenEmbedding.preimage_closedPoints`：Topology.IsOpenEmbedding
.preimage_closedPoints (hf : IsOpenEmbedding f) [JacobsonSpace Y] : f ⁻¹' closed
Points Y = closedPoints X
· 使用引理 `nonempty_inter_closedPoints`：nonempty_inter_closedPoints [JacobsonSpace 
X] {Z : Set X} (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z inter closedPoin
ts X).Nonempty
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用引理 `IsLocallyClosed.image`：IsLocallyClosed.image {s : Set X} (hs : IsLocally
Closed s) {f : X -> Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) : I
sLocallyClo…
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
-/
lemma JacobsonSpace.of_isOpenEmbedding [JacobsonSpace Y] (hf : IsOpenEmbedding f) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed, ← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isOpen_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩
/-
**JacobsonSpace.of_isClosedEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：JacobsonSpace.of_isClosedEmbedding [JacobsonSpace Y] (hf : IsClosedEmbeddi
ng f) : JacobsonSpace X
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `jacobsonSpace_iff_locallyClosed`：jacobsonSpace_iff_locallyClosed : Jacob
sonSpace X ↔ forall Z, Z.Nonempty -> IsLocallyClosed Z -> (Z inter closedPoints 
X).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsClosedEmbedding.preimage_closedPoints`：Topology.IsClosedEmbed
ding.preimage_closedPoints (hf : IsClosedEmbedding f) : f ⁻¹' closedPoints Y = c
losedPoints X
· 使用引理 `nonempty_inter_closedPoints`：nonempty_inter_closedPoints [JacobsonSpace 
X] {Z : Set X} (hZ : Z.Nonempty) (hZ' : IsLocallyClosed Z) : (Z inter closedPoin
ts X).Nonempty
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用引理 `IsLocallyClosed.image`：IsLocallyClosed.image {s : Set X} (hs : IsLocally
Closed s) {f : X -> Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) : I
sLocallyClo…
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
-/
lemma JacobsonSpace.of_isClosedEmbedding [JacobsonSpace Y] (hf : IsClosedEmbedding f) :
    JacobsonSpace X := by
  rw [jacobsonSpace_iff_locallyClosed, ← hf.preimage_closedPoints]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := nonempty_inter_closedPoints
    (hZ.image f) (hZ'.image hf.isInducing hf.isClosed_range.isLocallyClosed)
  exact ⟨_, hx, hx'⟩
/-
**JacobsonSpace.discreteTopology** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：JacobsonSpace.discreteTopology [JacobsonSpace X] (h : (closedPoints X).Fin
ite) : DiscreteTopology X
参数：h : (closedPoints X).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用引理 `closure_closedPoints`：closure_closedPoints [JacobsonSpace X] : closure (
closedPoints X) = Set.univ
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `discreteTopology_iff_forall_isOpen`：discreteTopology_iff_forall_isOpen [
TopologicalSpace α] : DiscreteTopology α ↔ forall s : Set α, IsOpen s
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `mem_closedPoints_iff`：mem_closedPoints_iff {x} : x in closedPoints X ↔ I
sClosed {x}
-/
lemma JacobsonSpace.discreteTopology [JacobsonSpace X]
    (h : (closedPoints X).Finite) : DiscreteTopology X := by
  have : closedPoints X = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints,
      closure_subset_iff_isClosed, ← (closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ ↦ id
  have inst : Finite X := Set.finite_univ_iff.mp (this ▸ h)
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  rw [← isClosed_compl_iff, ← sᶜ.biUnion_of_singleton]
  refine sᶜ.toFinite.isClosed_biUnion fun x _ ↦ ?_
  rw [← mem_closedPoints_iff, this]
  trivial
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Finite X] [JacobsonSpace X] : DiscreteTopology X :=
  JacobsonSpace.discreteTopology (Set.toFinite _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [T1Space X] : JacobsonSpace X :=
  ⟨by simp [closedPoints_eq_univ, closure_eq_iff_isClosed]⟩
/-
**TopologicalSpace.IsOpenCover.jacobsonSpace_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopologicalSpace.IsOpenCover.jacobsonSpace_iff {ι : Type*} {U : ι -> Opens
 X} (hU : IsOpenCover U) : JacobsonSpace X ↔ forall i, JacobsonSpace (U i)
参数：hU : IsOpenCover U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `JacobsonSpace.of_isOpenEmbedding`：JacobsonSpace.of_isOpenEmbedding [Jaco
bsonSpace Y] (hf : IsOpenEmbedding f) : JacobsonSpace X
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `jacobsonSpace_iff_locallyClosed`：jacobsonSpace_iff_locallyClosed : Jacob
sonSpace X ↔ forall Z, Z.Nonempty -> IsLocallyClosed Z -> (Z inter closedPoints 
X).Nonempty
· 使用定理 `Set.nonempty_iUnion`：nonempty_iUnion : (⋃ i, s i).Nonempty ↔ exists i, (
s i).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TopologicalSpace.IsOpenCover.iUnion_inter`：iUnion_inter (hu : IsOpenCove
r u) (s : Set X) : ⋃ i, s inter u i = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocallyClosed.preimage`：IsLocallyClosed.preimage {s : Set Y} (hs : IsL
ocallyClosed s) {f : X -> Y} (hf : Continuous f) : IsLocallyClosed (f ⁻¹' s)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage`：isClosed_iff_coe
_preimage {s : Set β} : IsClosed s ↔ forall i, IsClosed ((↑) ⁻¹' s : Set (U i))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `isClosed_singleton_of_isLocallyClosed_singleton`：isClosed_singleton_of_i
sLocallyClosed_singleton [JacobsonSpace X] {x : X} (hx : IsLocallyClosed {x}) : 
IsClosed {x}
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用引理 `IsLocallyClosed.image`：IsLocallyClosed.image {s : Set X} (hs : IsLocally
Closed s) {f : X -> Y} (hf : IsInducing f) (hf' : IsLocallyClosed (range f)) : I
sLocallyClo…
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
（共 32 条，此处仅展示前 30 条）
-/
lemma TopologicalSpace.IsOpenCover.jacobsonSpace_iff {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) : JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i) := by
  refine ⟨fun H i ↦ .of_isOpenEmbedding (U i).2.isOpenEmbedding_subtypeVal, fun H ↦ ?_⟩
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  rw [← hU.iUnion_inter Z, Set.nonempty_iUnion] at hZ
  obtain ⟨i, x, hx, hx'⟩ := hZ
  obtain ⟨y, hy, hy'⟩ := (jacobsonSpace_iff_locallyClosed.mp (H i)) _ ⟨⟨x, hx'⟩, hx⟩
    (hZ'.preimage continuous_subtype_val)
  refine ⟨y, hy, hU.isClosed_iff_coe_preimage.mpr fun j ↦ ?_⟩
  by_cases h : (y : X) ∈ U j
  · convert_to IsClosed {(⟨y, h⟩ : U j)}
    · ext; simp [← Subtype.coe_inj]
    apply isClosed_singleton_of_isLocallyClosed_singleton
    convert!
      (hy'.isLocallyClosed.image IsEmbedding.subtypeVal.isInducing
            (U i).2.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed).preimage
        continuous_subtype_val
    ext
    simp [← Subtype.coe_inj]
  · convert! isClosed_empty
    rw [Set.eq_empty_iff_forall_notMem]
    intro z (hz : z.1 = y.1)
    exact h (hz ▸ z.2)
/-
**subsingleton_image_closure_of_finite_of_isPreirreducible** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：subsingleton_image_closure_of_finite_of_isPreirreducible [JacobsonSpace X]
 {S : Set X} (hS : IsLocallyClosed S) (hS' : IsPreirreducible S) (hf₁ : Continuo
us f) (hf₂ : IsClosedMap f) (hfS : (f '' S).Finite) : (f '' closure S).Subsingle
ton
参数：hS : IsLocallyClosed S；hS' : IsPreirreducible S；hf₁ : Continuous f；hf₂ : IsCl
osedMap f；hfS : (f '' S).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isIrreducible_iff_closure`：isIrreducible_iff_closure : IsIrreducible (cl
osure s) ↔ IsIrreducible s
· 使用定理 `JacobsonSpace.closure_inter_closedPoints_eq_closure`：JacobsonSpace.closu
re_inter_closedPoints_eq_closure [JacobsonSpace X] {S : Set X} (hS : IsLocallyCl
osed S) : closure (S inter closedPoints X…
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsDiscrete.subsingleton_of_isPreirreducible`：IsDiscrete.subsingleton_of_
isPreirreducible (hs : IsDiscrete s) (hs' : IsPreirreducible s) : s.Subsingleton
· 使用引理 `Set.Finite.isDiscrete_of_subset_closedPoints`：Set.Finite.isDiscrete_of_s
ubset_closedPoints {s : Set X} (hs : s.Finite) (hs' : s subseteq closedPoints X)
 : IsDiscrete s
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
· 使用定理 `IsIrreducible.image`：IsIrreducible.image (H : IsIrreducible s) (f : X ->
 Y) (hf : ContinuousOn f s) : IsIrreducible (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
-/
theorem subsingleton_image_closure_of_finite_of_isPreirreducible [JacobsonSpace X]
    {S : Set X} (hS : IsLocallyClosed S) (hS' : IsPreirreducible S)
    (hf₁ : Continuous f) (hf₂ : IsClosedMap f) (hfS : (f '' S).Finite) :
    (f '' closure S).Subsingleton := by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  replace hS' : IsIrreducible S := ⟨hS'', hS'⟩
  have H₁ : IsIrreducible (S ∩ closedPoints X) := by
    rwa [← isIrreducible_iff_closure, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      isIrreducible_iff_closure] at hS'
  have H₂ : f '' (S ∩ closedPoints X) ⊆ closedPoints Y := by
    rintro _ ⟨x, hx, rfl⟩; simpa using hf₂ _ hx.2
  have H₃ := ((hfS.subset (Set.image_mono Set.inter_subset_left)).isDiscrete_of_subset_closedPoints
    H₂).subsingleton_of_isPreirreducible (H₁.image _ hf₁.continuousOn).isPreirreducible
  have H₄ : IsClosed (f '' (S ∩ closedPoints X)) := by
    obtain (h | ⟨x, hx⟩) := Set.eq_empty_or_nonempty (f '' (S ∩ closedPoints X))
    · simp [h]
    · rw [H₃.eq_singleton_of_mem hx]; exact H₂ hx
  have := image_closure_subset_closure_image (s := S ∩ closedPoints X) hf₁
  rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hS, H₄.closure_eq] at this
  exact H₃.anti this
