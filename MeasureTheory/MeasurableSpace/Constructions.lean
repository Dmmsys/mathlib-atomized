/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Prod.TProd
public import Mathlib.Data.Set.UnionLift
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Order.Disjointed

/-!
# Constructions for measurable spaces and functions

This file provides several ways to construct new measurable spaces and functions from old ones:
`Quotient`, `Subtype`, `Prod`, `Pi`, etc.
-/

@[expose] public section

assert_not_exists Filter

open Set Function

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

/-
**measurable_to_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace
 β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' {f y})) : Measurable f
参数：h : forall y, MeasurableSet (f ⁻¹' {f y})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_singleton_eq_empty`：preimage_singleton_eq_empty {f : α -> β
} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f
-/
theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f := fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]
/-
**measurable_to_countable'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpac
e β] {f : β -> α} (h : forall x, MeasurableSet (f ⁻¹' {x})) : Measurable f
参数：h : forall x, MeasurableSet (f ⁻¹' {x})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable`：measurable_to_countable [MeasurableSpace α] [Co
untable α] [MeasurableSpace β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' 
{f y})) : Mea…
-/
theorem measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)

set_option backward.isDefEq.respectTransparency false in
/-
**ENat.measurable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENat.measurable_iff {α : Type*} [MeasurableSpace α] {f : α -> Nat∞} : Meas
urable f ↔ forall n : Nat, MeasurableSet (f ⁻¹' {↑n})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `measurable_to_countable'`：measurable_to_countable' [MeasurableSpace α] [
Countable α] [MeasurableSpace β] {f : β -> α} (h : forall x, MeasurableSet (f ⁻¹
' {x})) : Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.none_eq_top`：∀ {α : Type u_1}, none = ⊤
· 使用定理 `Set.compl_range_some`：compl_range_some (α : Type*) : (range (some : α ->
 Option α))ᶜ = {none}
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem ENat.measurable_iff {α : Type*} [MeasurableSpace α] {f : α → ℕ∞} :
    Measurable f ↔ ∀ n : ℕ, MeasurableSet (f ⁻¹' {↑n}) := by
  refine ⟨fun hf n ↦ hf <| measurableSet_singleton _, fun h ↦ measurable_to_countable' fun n ↦ ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top, ← compl_range_some, preimage_compl, ← iUnion_singleton_eq_range,
      preimage_iUnion]
    exact .compl <| .iUnion h
  | coe n => exact h n
/-
**measurable_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_unit [MeasurableSpace α] (f : Unit -> α) : Measurable f
参数：f : Unit -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_from_top`：measurable_from_top [MeasurableSpace β] {f : α -> β
} : Measurable[⊤] f
-/
theorem measurable_unit [MeasurableSpace α] (f : Unit → α) : Measurable f :=
  measurable_from_top

section ULift
variable [MeasurableSpace α]

/-
**_root_.ULift.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：_root_.ULift.instMeasurableSpace : MeasurableSpace (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.ULift.instMeasurableSpace : MeasurableSpace (ULift α) :=
  ‹MeasurableSpace α›.map ULift.up
/-
**measurable_down** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_down : Measurable (ULift.down : ULift α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma measurable_down : Measurable (ULift.down : ULift α → α) := fun _ ↦ id
/-
**measurable_up** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_up : Measurable (ULift.up : α -> ULift α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma measurable_up : Measurable (ULift.up : α → ULift α) := fun _ ↦ id
/-
**measurableSet_preimage_down** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {s : Set α}, MeasurableSet (UL
ift.down ⁻¹' s) ↔ MeasurableSet s
参数：ULift.down ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma measurableSet_preimage_down {s : Set α} :
    MeasurableSet (ULift.down ⁻¹' s) ↔ MeasurableSet s := Iff.rfl
/-
**measurableSet_preimage_up** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {s : Set (ULift.{u_6, u_1} α)}
,   MeasurableSet (ULift.up ⁻¹' s) ↔ MeasurableSet s
参数：ULift.{u_6, u_1} α；ULift.up ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma measurableSet_preimage_up {s : Set (ULift α)} :
    MeasurableSet (ULift.up ⁻¹' s) ↔ MeasurableSet s := Iff.rfl

end ULift

section Nat

variable {mα : MeasurableSpace α}

/-
**measurable_from_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_from_nat {f : Nat -> α} : Measurable f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_from_top`：measurable_from_top [MeasurableSpace β] {f : α -> β
} : Measurable[⊤] f
-/
theorem measurable_from_nat {f : ℕ → α} : Measurable f :=
  measurable_from_top
/-
**measurable_to_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_to_nat {f : α -> Nat} : (forall y, MeasurableSet (f ⁻¹' {f y}))
 -> Measurable f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable`：measurable_to_countable [MeasurableSpace α] [Co
untable α] [MeasurableSpace β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' 
{f y})) : Mea…
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem measurable_to_nat {f : α → ℕ} : (∀ y, MeasurableSet (f ⁻¹' {f y})) → Measurable f :=
  measurable_to_countable
/-
**measurable_to_bool** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_to_bool {f : α -> Bool} (h : MeasurableSet (f ⁻¹' {true})) : Me
asurable f
参数：h : MeasurableSet (f ⁻¹' {true})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable'`：measurable_to_countable' [MeasurableSpace α] [
Countable α] [MeasurableSpace β] {f : β -> α} (h : forall x, MeasurableSet (f ⁻¹
' {x})) : Meas…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Bool.compl_singleton`：compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {
!b}
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem measurable_to_bool {f : α → Bool} (h : MeasurableSet (f ⁻¹' {true})) : Measurable f := by
  apply measurable_to_countable'
  rintro (- | -)
  · convert! h.compl
    rw [← preimage_compl, Bool.compl_singleton, Bool.not_true]
  exact h
/-
**measurable_to_prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_to_prop {f : α -> Prop} (h : MeasurableSet (f ⁻¹' {True})) : Me
asurable f
参数：h : MeasurableSet (f ⁻¹' {True})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable'`：measurable_to_countable' [MeasurableSpace α] [
Countable α] [MeasurableSpace β] {f : β -> α} (h : forall x, MeasurableSet (f ⁻¹
' {x})) : Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.preimage_singleton_true`：∀ {α : Type u_1} (p : α → Prop), p ⁻¹' {Tru
e} = {a | p a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.preimage_singleton_false`：∀ {α : Type u_1} (p : α → Prop), p ⁻¹' {Fa
lse} = {a | ¬p a}
· 使用定理 `Prop.compl_singleton`：∀ (p : Prop), {p}ᶜ = {¬p}
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem measurable_to_prop {f : α → Prop} (h : MeasurableSet (f ⁻¹' {True})) : Measurable f := by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl
/-
**measurable_findGreatest'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_findGreatest' {p : α -> Nat -> Prop} [forall x, DecidablePred (
p x)] {N : Nat} (hN : forall k <= N, MeasurableSet { x | Nat.findGreatest (p x) 
N = k }) : Measurable fun x => Nat.findGreatest (p x) N
参数：p x；hN : forall k <= N, MeasurableSet { x | Nat.findGreatest (p x) N = k }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_nat`：measurable_to_nat {f : α -> Nat} : (forall y, Measura
bleSet (f ⁻¹' {f y})) -> Measurable f
· 使用引理 `Nat.findGreatest_le`：findGreatest_le (n : Nat) : Nat.findGreatest P n <=
 n
-/
theorem measurable_findGreatest' {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N : ℕ}
    (hN : ∀ k ≤ N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun _ => hN _ N.findGreatest_le
/-
**measurable_findGreatest** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_findGreatest {p : α -> Nat -> Prop} [forall x, DecidablePred (p
 x)] {N} (hN : forall k <= N, MeasurableSet { x | p x k }) : Measurable fun x =>
 Nat.findGreatest (p x) N
参数：p x；hN : forall k <= N, MeasurableSet { x | p x k }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_findGreatest'`：measurable_findGreatest' {p : α -> Nat -> Prop
} [forall x, DecidablePred (p x)] {N : Nat} (hN : forall k <= N, MeasurableSet {
 x | Nat.findG…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem measurable_findGreatest {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] {N}
    (hN : ∀ k ≤ N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N := by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, ofPred_and, ofPred_forall, ← compl_ofPred]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros

@[simp, measurability]
/-
**MeasurableSet.disjointed** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {f : ℕ → Set α},   (∀ (i : ℕ), M
easurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disjointed f n)
参数：∀ (i : ℕ), MeasurableSet (f i)；n : ℕ；disjointed f n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `disjointedRec`：disjointedRec {f : ι -> α} {p : α -> Prop} (hdiff : foral
l ⦃t i⦄, p t -> p (t \ f i)) : forall ⦃i⦄, p (f i) -> p (disjointed f i)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
-/
protected theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)

set_option backward.isDefEq.respectTransparency false in
/-
**measurable_find** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_find {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] (hp
 : forall x, exists N, p x N) (hm : forall k, MeasurableSet { x | p x k }) : Mea
surable fun x => Nat.find (hp x)
参数：p x；hp : forall x, exists N, p x N；hm : forall k, MeasurableSet { x | p x k }
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_nat`：measurable_to_nat {f : α -> Nat} : (forall y, Measura
bleSet (f ⁻¹' {f y})) -> Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preimage_find_eq_disjointed`：preimage_find_eq_disjointed (s : Nat -> Set
 α) (H : forall x, exists n, x in s n) [forall x n, Decidable (x in s n)] (n : N
at) : (fun x => N…
· 使用定理 `MeasurableSet.disjointed`：∀ {α : Type u_1} {mα : MeasurableSpace α} {f :
 ℕ → Set α},   (∀ (i : ℕ), MeasurableSet (f i)) → ∀ (n : ℕ), MeasurableSet (disj
ointed f n)
-/
theorem measurable_find {p : α → ℕ → Prop} [∀ x, DecidablePred (p x)] (hp : ∀ x, ∃ N, p x N)
    (hm : ∀ k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) := by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _

end Nat

section Quotient

variable [MeasurableSpace α] [MeasurableSpace β]

/-
**Quot.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quot.instMeasurableSpace {α} {r : α -> α -> Prop} [m : MeasurableSpace α] 
: MeasurableSpace (Quot r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quot.instMeasurableSpace {α} {r : α → α → Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Quot r) :=
  m.map (Quot.mk r)
/-
**Quotient.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.instMeasurableSpace {α} {s : Setoid α} [m : MeasurableSpace α] : 
MeasurableSpace (Quotient s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance Quotient.instMeasurableSpace {α} {s : Setoid α} [m : MeasurableSpace α] :
    MeasurableSpace (Quotient s) :=
  m.map Quotient.mk''

@[to_additive]
/-
**QuotientGroup.measurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgr
oup G) : MeasurableSpace (G ⧸ S)
参数：S : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgroup G) :
    MeasurableSpace (G ⧸ S) :=
  Quotient.instMeasurableSpace
/-
**measurableSet_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} : MeasurableS
et t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t)
参数：Quotient s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} :
    MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) :=
  Iff.rfl
/-
**measurable_from_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_from_quotient {s : Setoid α} {f : Quotient s -> β} : Measurable
 f ↔ Measurable (f ∘ Quotient.mk'')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurable_from_quotient {s : Setoid α} {f : Quotient s → β} :
    Measurable f ↔ Measurable (f ∘ Quotient.mk'') :=
  Iff.rfl

@[fun_prop]
/-
**measurable_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α -> Q
uotient s)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α → Quotient s) :=
  fun _ => id

@[fun_prop]
/-
**measurable_quotient_mk''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α ->
 Quotient s)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α → Quotient s) :=
  fun _ => id

@[fun_prop]
/-
**measurable_quot_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_quot_mk {r : α -> α -> Prop} : Measurable (Quot.mk r)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_quot_mk {r : α → α → Prop} : Measurable (Quot.mk r) := fun _ => id

@[to_additive (attr := fun_prop)]
/-
**QuotientGroup.measurable_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgro
up G} : Measurable ((↑) : G -> G ⧸ S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_quotient_mk''`：measurable_quotient_mk'' {s : Setoid α} : Meas
urable (Quotient.mk'' : α -> Quotient s)
-/
theorem QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgroup G} :
    Measurable ((↑) : G → G ⧸ S) :=
  measurable_quotient_mk''

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G]
    {S : Subgroup G} {f : G ⧸ S → α} : Measurable f ↔ Measurable (f ∘ ((↑) : G → G ⧸ S)) :=
  measurable_from_quotient
/-
**Quotient.instDiscreteMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.instDiscreteMeasurableSpace {α} {s : Setoid α} [MeasurableSpace α
] [DiscreteMeasurableSpace α] : DiscreteMeasurableSpace (Quotient s) where foral
l_measurableSet _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `measurableSet_quotient`：measurableSet_quotient {s : Setoid α} {t : Set (
Quotient s)} : MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t)
· 使用定理 `MeasurableSet.of_discrete`：∀ {α : Type u_1} [inst : MeasurableSpace α] [
DiscreteMeasurableSpace α] {s : Set α}, MeasurableSet s
-/
instance Quotient.instDiscreteMeasurableSpace {α} {s : Setoid α} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] : DiscreteMeasurableSpace (Quotient s) where
  forall_measurableSet _ := measurableSet_quotient.2 .of_discrete

@[to_additive]
/-
**QuotientGroup.instDiscreteMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientGroup.instDiscreteMeasurableSpace {G} [Group G] [MeasurableSpace G
] [DiscreteMeasurableSpace G] (S : Subgroup G) : DiscreteMeasurableSpace (G ⧸ S)
参数：S : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance QuotientGroup.instDiscreteMeasurableSpace {G} [Group G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (S : Subgroup G) : DiscreteMeasurableSpace (G ⧸ S) :=
  Quotient.instDiscreteMeasurableSpace

end Quotient

section Subtype

/-
**Subtype.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.instMeasurableSpace {α} {p : α -> Prop} [m : MeasurableSpace α] : 
MeasurableSpace (Subtype p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subtype.instMeasurableSpace {α} {p : α → Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Subtype p) :=
  m.comap ((↑) : _ → α)

section

variable [MeasurableSpace α]

/-
**measurable_subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_subtype_coe {p : α -> Prop} : Measurable ((↑) : Subtype p -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.le_map_comap`：le_map_comap : m <= (m.comap g).map g
-/
theorem measurable_subtype_coe {p : α → Prop} : Measurable ((↑) : Subtype p → α) :=
  MeasurableSpace.le_map_comap
/-
**Subtype.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.instMeasurableSingletonClass {p : α -> Prop} [MeasurableSingletonC
lass α] : MeasurableSingletonClass (Subtype p) where measurableSet_singleton x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
instance Subtype.instMeasurableSingletonClass {p : α → Prop} [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Subtype p) where
  measurableSet_singleton x :=
    ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton, preimage_image_eq _ Subtype.val_injective]⟩

end

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

/-
**MeasurableSet.of_subtype_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.of_subtype_image {s : Set α} {t : Set s} (h : MeasurableSet 
(Subtype.val '' t)) : MeasurableSet t
参数：h : MeasurableSet (Subtype.val '' t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem MeasurableSet.of_subtype_image {s : Set α} {t : Set s}
    (h : MeasurableSet (Subtype.val '' t)) : MeasurableSet t :=
  ⟨_, h, preimage_image_eq _ Subtype.val_injective⟩
/-
**MeasurableSet.subtype_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s)
 : MeasurableSet t -> MeasurableSet (((↑) : s -> α) '' t)
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s) :
    MeasurableSet t → MeasurableSet (((↑) : s → α) '' t) := by
  rintro ⟨u, hu, rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hu

@[fun_prop]
/-
**Measurable.subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.subtype_coe {p : β -> Prop} {f : α -> Subtype p} (hf : Measurab
le f) : Measurable fun a : α => (f a : β)
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem Measurable.subtype_coe {p : β → Prop} {f : α → Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf

alias Measurable.subtype_val := Measurable.subtype_coe

@[fun_prop]
/-
**Measurable.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.subtype_mk {p : β -> Prop} {f : α -> β} (hf : Measurable f) {h 
: forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ : Subtype p)
参数：hf : Measurable f；f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Measurable.subtype_mk {p : β → Prop} {f : α → β} (hf : Measurable f) {h : ∀ x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, Function.comp_def, hf hs.1]

@[fun_prop]
/-
**Measurable.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.codRestrict {s : Set β} {f : α -> β} (hf : Measurable f) (h : f
orall y, f y in s) : Measurable (codRestrict f s h)
参数：hf : Measurable f；h : forall y, f y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
-/
theorem Measurable.codRestrict {s : Set β} {f : α → β} (hf : Measurable f)
    (h : ∀ y, f y ∈ s) : Measurable (codRestrict f s h) := hf.subtype_mk

@[fun_prop]
/-
**Measurable.rangeFactorization** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {mβ : MeasurableSp
ace β} {f : α → β},   Measurable f → Measurable (Set.rangeFactorization f)
参数：Set.rangeFactorization f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
protected theorem Measurable.rangeFactorization {f : α → β} (hf : Measurable f) :
    Measurable (rangeFactorization f) :=
  hf.subtype_mk
/-
**Measurable.subtype_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.subtype_map {f : α -> β} {p : α -> Prop} {q : β -> Prop} (hf : 
Measurable f) (hpq : forall x, p x -> q (f x)) : Measurable (Subtype.map f hpq)
参数：hf : Measurable f；hpq : forall x, p x -> q (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem Measurable.subtype_map {f : α → β} {p : α → Prop} {q : β → Prop} (hf : Measurable f)
    (hpq : ∀ x, p x → q (f x)) : Measurable (Subtype.map f hpq) :=
  (hf.comp measurable_subtype_coe).subtype_mk
/-
**measurable_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_inclusion {s t : Set α} (h : s subseteq t) : Measurable (inclus
ion h)
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.subtype_map`：Measurable.subtype_map {f : α -> β} {p : α -> Pr
op} {q : β -> Prop} (hf : Measurable f) (hpq : forall x, p x -> q (f x)) : Measu
rable (Subty…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem measurable_inclusion {s t : Set α} (h : s ⊆ t) : Measurable (inclusion h) :=
  measurable_id.subtype_map h
/-
**MeasurableSet.image_inclusion'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_inclusion' {s t : Set α} (h : s subseteq t) {u : Set s
} (hs : MeasurableSet (Subtype.val ⁻¹' s : Set t)) (hu : MeasurableSet u) : Meas
urableSet (inclusion h '' u)
参数：h : s subseteq t；hs : MeasurableSet (Subtype.val ⁻¹' s : Set t)；hu : Measurab
leSet u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem MeasurableSet.image_inclusion' {s t : Set α} (h : s ⊆ t) {u : Set s}
    (hs : MeasurableSet (Subtype.val ⁻¹' s : Set t)) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) := by
  rcases hu with ⟨u, hu, rfl⟩
  convert! (measurable_subtype_coe hu).inter hs
  ext ⟨x, hx⟩
  simpa [@and_comm _ (_ = x)] using and_comm
/-
**MeasurableSet.image_inclusion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_inclusion {s t : Set α} (h : s subseteq t) {u : Set s}
 (hs : MeasurableSet s) (hu : MeasurableSet u) : MeasurableSet (inclusion h '' u
)
参数：h : s subseteq t；hs : MeasurableSet s；hu : MeasurableSet u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.image_inclusion'`：MeasurableSet.image_inclusion' {s t : Se
t α} (h : s subseteq t) {u : Set s} (hs : MeasurableSet (Subtype.val ⁻¹' s : Set
 t)) (hu : Measurabl…
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem MeasurableSet.image_inclusion {s t : Set α} (h : s ⊆ t) {u : Set s}
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) :=
  (measurable_subtype_coe hs).image_inclusion' h hu
/-
**MeasurableSet.of_union_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.of_union_cover {s t u : Set α} (hs : MeasurableSet s) (ht : 
MeasurableSet t) (h : univ subseteq s union t) (hsu : MeasurableSet (((↑) : s ->
 α) ⁻¹' u)) (htu : MeasurableSet (((↑) : t -> α) ⁻¹' u)) : MeasurableSet u
参数：hs : MeasurableSet s；ht : MeasurableSet t；h : univ subseteq s union t；hsu : M
easurableSet (((↑) : s -> α) ⁻¹' u)；htu : MeasurableSet (((↑) : t -> α) ⁻¹' u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)
-/
theorem MeasurableSet.of_union_cover {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ ⊆ s ∪ t) (hsu : MeasurableSet (((↑) : s → α) ⁻¹' u))
    (htu : MeasurableSet (((↑) : t → α) ⁻¹' u)) : MeasurableSet u := by
  convert! (hs.subtype_image hsu).union (ht.subtype_image htu)
  simp [image_preimage_eq_inter_range, ← inter_union_distrib_left, univ_subset_iff.1 h]
/-
**measurable_of_measurable_union_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_measurable_union_cover {f : α -> β} (s t : Set α) (hs : Meas
urableSet s) (ht : MeasurableSet t) (h : univ subseteq s union t) (hc : Measurab
le fun a : s => f a) (hd : Measurable fun a : t => f a) : Measurable f
参数：s t : Set α；hs : MeasurableSet s；ht : MeasurableSet t；h : univ subseteq s uni
on t；hc : Measurable fun a : s => f a；hd : Measurable fun a : t => f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_union_cover`：MeasurableSet.of_union_cover {s t u : Set 
α} (hs : MeasurableSet s) (ht : MeasurableSet t) (h : univ subseteq s union t) (
hsu : MeasurableSe…
-/
theorem measurable_of_measurable_union_cover {f : α → β} (s t : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : univ ⊆ s ∪ t) (hc : Measurable fun a : s => f a)
    (hd : Measurable fun a : t => f a) : Measurable f := fun _u hu =>
  .of_union_cover hs ht h (hc hu) (hd hu)
/-
**measurable_of_restrict_of_restrict_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_restrict_of_restrict_compl {f : α -> β} {s : Set α} (hs : Me
asurableSet s) (h₁ : Measurable (s.domRestrict f)) (h₂ : Measurable (sᶜ.domRestr
ict f)) : Measurable f
参数：hs : MeasurableSet s；h₁ : Measurable (s.domRestrict f)；h₂ : Measurable (sᶜ.do
mRestrict f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_measurable_union_cover`：measurable_of_measurable_union_cov
er {f : α -> β} (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) (h :
 univ subseteq s union t) …
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
-/
theorem measurable_of_restrict_of_restrict_compl {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.domRestrict f)) (h₂ : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂
/-
**Measurable.dite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.dite [forall x, Decidable (x in s)] {f : s -> β} (hf : Measurab
le f) {g : (sᶜ : Set α) -> β} (hg : Measurable g) (hs : MeasurableSet s) : Measu
rable fun x => if hx : x in s then f ⟨x, hx⟩ else g ⟨x, hx⟩
参数：x in s；hf : Measurable f；sᶜ : Set α；hg : Measurable g；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.domRestrict_dite`：domRestrict_dite {s : Set α} [forall x, Decidable 
(x in s)] (f : forall a in s, β) (g : forall a ∉ s, β) : (s.domRestrict fun a =>
 if h : a …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Set.domRestrict_dite_compl`：domRestrict_dite_compl {s : Set α} [forall x
, Decidable (x in s)] (f : forall a in s, β) (g : forall a ∉ s, β) : (sᶜ.domRest
rict fun a => if…
-/
theorem Measurable.dite [∀ x, Decidable (x ∈ s)] {f : s → β} (hf : Measurable f)
    {g : (sᶜ : Set α) → β} (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x ∈ s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)
/-
**measurable_of_measurable_on_compl_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f :
 α -> β} (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.domRestrict f)) : Meas
urable f
参数：s : Set α；hs : s.Finite；hf : Measurable (sᶜ.domRestrict f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `measurable_of_finite`：measurable_of_finite [Finite α] [MeasurableSinglet
onClass α] (f : α -> β) : Measurable f
-/
theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf
/-
**measurable_of_measurable_on_compl_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_measurable_on_compl_countable [MeasurableSingletonClass α] {
f : α -> β} (s : Set α) (hs : s.Countable) (hf : Measurable (sᶜ.domRestrict f)) 
: Measurable f
参数：s : Set α；hs : s.Countable；hf : Measurable (sᶜ.domRestrict f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `measurable_of_countable`：measurable_of_countable [Countable α] [Measurab
leSingletonClass α] (f : α -> β) : Measurable f
-/
theorem measurable_of_measurable_on_compl_countable [MeasurableSingletonClass α] {f : α → β}
    (s : Set α) (hs : s.Countable) (hf : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_countable _) hf
/-
**measurable_of_measurable_on_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {
f : α -> β} (a : α) (hf : Measurable ({ x | x != a }.domRestrict f)) : Measurabl
e f
参数：a : α；hf : Measurable ({ x | x != a }.domRestrict f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_measurable_on_compl_finite`：measurable_of_measurable_on_co
mpl_finite [MeasurableSingletonClass α] {f : α -> β} (s : Set α) (hs : s.Finite)
 (hf : Measurable (sᶜ.domRestr…
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α → β} (a : α)
    (hf : Measurable ({ x | x ≠ a }.domRestrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf

end Subtype

section Atoms

variable [MeasurableSpace β]

/-- The *measurable atom* of `x` is the intersection of all the measurable sets containing `x`.
It is measurable when the space is countable (or more generally when the measurable space is
countably generated). -/
/-
**measurableAtom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：measurableAtom (x : β) : Set β
参数：x : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *measurable atom* of `x` is the intersection of all the measurable sets cont
aining `x`.
It is measurable when the space is countable (or more generally when the measura
ble space is
countably generated).
-/
def measurableAtom (x : β) : Set β :=
  ⋂ (s : Set β) (_h's : x ∈ s) (_hs : MeasurableSet s), s
/-
**mem_measurableAtom_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {β : Type u_2} [inst : MeasurableSpace β] (x : β), x ∈ measurableAtom x
参数：x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma mem_measurableAtom_self (x : β) : x ∈ measurableAtom x := by
  simp +contextual [measurableAtom]
/-
**mem_of_mem_measurableAtom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_of_mem_measurableAtom {x y : β} (h : y in measurableAtom x) {s : Set β
} (hs : MeasurableSet s) (hxs : x in s) : y in s
参数：h : y in measurableAtom x；hs : MeasurableSet s；hxs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma mem_of_mem_measurableAtom {x y : β} (h : y ∈ measurableAtom x) {s : Set β}
    (hs : MeasurableSet s) (hxs : x ∈ s) : y ∈ s := by
  simp only [measurableAtom, mem_iInter] at h
  exact h s hxs hs
/-
**measurableAtom_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableAtom_subset {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x i
n s) : measurableAtom x subseteq s
参数：hs : MeasurableSet s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter₂_subset_of_subset`：iInter₂_subset_of_subset {s : forall i, κ 
i -> Set α} {t : Set α} (i : ι) (j : κ i) (h : s i j subseteq t) : ⋂ (i) (j), s 
i j subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
-/
lemma measurableAtom_subset {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x ∈ s) :
    measurableAtom x ⊆ s :=
  iInter₂_subset_of_subset s hx fun ⦃a⦄ ↦ (by simp [hs])
/-
**measurableAtom_of_measurableSingletonClass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {β : Type u_2} [inst : MeasurableSpace β] [MeasurableSingletonClass β] (
x : β), measurableAtom x = {x}
参数：x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `measurableAtom_subset`：measurableAtom_subset {s : Set β} {x : β} (hs : M
easurableSet s) (hx : x in s) : measurableAtom x subseteq s
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma measurableAtom_of_measurableSingletonClass [MeasurableSingletonClass β] (x : β) :
    measurableAtom x = {x} :=
  Subset.antisymm (measurableAtom_subset (measurableSet_singleton x) rfl) (by simp)
/-
**MeasurableSet.measurableAtom_of_countable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.measurableAtom_of_countable [Countable β] (x : β) : Measurab
leSet (measurableAtom x)
参数：x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `mem_of_mem_measurableAtom`：mem_of_mem_measurableAtom {x y : β} (h : y in
 measurableAtom x) {s : Set β} (hs : MeasurableSet s) (hxs : x in s) : y in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma MeasurableSet.measurableAtom_of_countable [Countable β] (x : β) :
    MeasurableSet (measurableAtom x) := by
  have : ∀ (y : β), y ∉ measurableAtom x → ∃ s, x ∈ s ∧ MeasurableSet s ∧ y ∉ s :=
    fun y hy ↦ by simpa [measurableAtom] using hy
  choose! s hs using this
  have : measurableAtom x = ⋂ (y ∈ (measurableAtom x)ᶜ), s y := by
    apply Subset.antisymm
    · intro z hz
      simp only [mem_iInter, mem_compl_iff]
      intro i hi
      exact mem_of_mem_measurableAtom hz (hs i hi).2.1 (hs i hi).1
    · apply compl_subset_compl.1
      intro z hz
      simp only [compl_iInter, mem_iUnion, mem_compl_iff, exists_prop]
      exact ⟨z, hz, (hs z hz).2.2⟩
  rw [this]
  exact MeasurableSet.biInter (to_countable (measurableAtom x)ᶜ) (fun i hi ↦ (hs i hi).2.1)

/-- There is in fact equality: see `measurableAtom_eq_of_mem`. -/
/-
**measurableAtom_subset_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableAtom_subset_of_mem {x y : β} (hx : x in measurableAtom y) : meas
urableAtom x subseteq measurableAtom y
参数：hx : x in measurableAtom y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
There is in fact equality: see `measurableAtom_eq_of_mem`.
-/
lemma measurableAtom_subset_of_mem {x y : β} (hx : x ∈ measurableAtom y) :
    measurableAtom x ⊆ measurableAtom y := by
  intro z hz
  simp only [measurableAtom, mem_iInter] at hz hx ⊢
  exact fun s hys hs ↦ hz s (hx s hys hs) hs
/-
**measurableAtom_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableAtom_eq_of_mem {x y : β} (hx : x in measurableAtom y) : measurab
leAtom x = measurableAtom y
参数：hx : x in measurableAtom y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `measurableAtom_subset_of_mem`：measurableAtom_subset_of_mem {x y : β} (hx
 : x in measurableAtom y) : measurableAtom x subseteq measurableAtom y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
lemma measurableAtom_eq_of_mem {x y : β} (hx : x ∈ measurableAtom y) :
    measurableAtom x = measurableAtom y := by
  refine subset_antisymm (measurableAtom_subset_of_mem hx) ?_
  by_cases hy : y ∈ measurableAtom x
  · exact measurableAtom_subset_of_mem hy
  exfalso
  simp only [measurableAtom, mem_iInter, not_forall] at hx hy ⊢
  obtain ⟨s, hxs, hs, hys⟩ := hy
  specialize hx sᶜ hys hs.compl
  exact hx hxs
/-
**disjoint_measurableAtom_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_measurableAtom_of_notMem {x y : β} (hx : x ∉ measurableAtom y) : 
Disjoint (measurableAtom x) (measurableAtom y)
参数：hx : x ∉ measurableAtom y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用引理 `measurableAtom_eq_of_mem`：measurableAtom_eq_of_mem {x y : β} (hx : x in 
measurableAtom y) : measurableAtom x = measurableAtom y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_measurableAtom_self`：∀ {β : Type u_2} [inst : MeasurableSpace β] (x 
: β), x ∈ measurableAtom x
-/
lemma disjoint_measurableAtom_of_notMem {x y : β} (hx : x ∉ measurableAtom y) :
    Disjoint (measurableAtom x) (measurableAtom y) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  have h1 := measurableAtom_eq_of_mem hzx
  have h2 := measurableAtom_eq_of_mem hzy
  rw [← h2, h1] at hx
  exact hx (mem_measurableAtom_self x)

end Atoms

section Prod

/-- A `MeasurableSpace` structure on the product of two measurable spaces. -/
@[instance_reducible]
/-
**MeasurableSpace.prod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace 
β) : MeasurableSpace (α × β)
参数：m₁ : MeasurableSpace α；m₂ : MeasurableSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MeasurableSpace` structure on the product of two measurable spaces.
-/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd
/-
**Prod.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSp
ace β] : MeasurableSpace (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α × β) :=
  m₁.prod m₂
/-
**measurable_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSpace β} : Measurabl
e (Prod.fst : α × β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.fst : α × β → α) :=
  Measurable.of_comap_le le_sup_left
/-
**measurable_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSpace β} : Measurabl
e (Prod.snd : α × β -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.snd : α × β → β) :=
  Measurable.of_comap_le le_sup_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[fun_prop]
/-
**Measurable.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Measurable fun a : α
 => (f a).1
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
theorem Measurable.fst {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf

@[fun_prop]
/-
**Measurable.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Measurable fun a : α
 => (f a).2
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem Measurable.snd {f : α → β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf
/-
**Measurable.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun a => (f a).1) (hf₂ 
: Measurable fun a => (f a).2) : Measurable f
参数：hf₁ : Measurable fun a => (f a).1；hf₂ : Measurable fun a => (f a).2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_le_map`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSp
ace α} {m₂ : MeasurableSpace β} {f : α → β},   m₂ ≤ MeasurableSpace.map f m₁ → M
easurable …
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.comap_le_iff_le_map`：comap_le_iff_le_map {f : α -> β} : 
m'.comap f <= m ↔ m' <= m.map f
· 使用定理 `MeasurableSpace.map_comp`：map_comp {f : α -> β} {g : β -> γ} : (m.map f)
.map g = m.map (g ∘ f)
-/
theorem Measurable.prod {f : α → β × γ} (hf₁ : Measurable fun a => (f a).1)
    (hf₂ : Measurable fun a => (f a).2) : Measurable f :=
  Measurable.of_le_map <|
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp]
        exact hf₂)

@[fun_prop]
/-
**Measurable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f
 : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun
 a : α => (f a, g a)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
-/
theorem Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α → β}
    {g : α → γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg

@[fun_prop]
/-
**Measurable.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (hf : Mea
surable f) (hg : Measurable g) : Measurable (Prod.map f g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem Measurable.prodMap [MeasurableSpace δ] {f : α → β} {g : γ → δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
/-
**measurable_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_prodMk_left {x : α} : Measurable (@Prod.mk _ β x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem measurable_prodMk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prodMk measurable_id
/-
**measurable_prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_prodMk_right {y : β} : Measurable fun x : α => (x, y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem measurable_prodMk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prodMk measurable_const

@[fun_prop]
/-
**measurable_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_diag : @Measurable α (α × α) m (m.prod m) Function.diag
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem measurable_diag : @Measurable α (α × α) m (m.prod m) Function.diag :=
  measurable_id.prodMk measurable_id
/-
**measurable_diag'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_diag' {m'} (h : m' <= m) : @Measurable α (α × α) m (m.prod m') 
Function.diag
参数：h : m' <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
-/
theorem measurable_diag' {m'} (h : m' ≤ m) : @Measurable α (α × α) m (m.prod m') Function.diag :=
  measurable_id.prodMk (measurable_id'' h)
/-
**Measurable.of_uncurry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.of_uncurry_left {f : α -> β -> γ} (hf : Measurable (uncurry f))
 {x : α} : Measurable (f x)
参数：hf : Measurable (uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
theorem Measurable.of_uncurry_left {f : α → β → γ} (hf : Measurable (uncurry f)) {x : α} :
    Measurable (f x) :=
  hf.comp measurable_prodMk_left
/-
**Measurable.of_uncurry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.of_uncurry_right {f : α -> β -> γ} (hf : Measurable (uncurry f)
) {y : β} : Measurable fun x => f x y
参数：hf : Measurable (uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem Measurable.of_uncurry_right {f : α → β → γ} (hf : Measurable (uncurry f)) {y : β} :
    Measurable fun x => f x y :=
  hf.comp measurable_prodMk_right
/-
**measurable_fun_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fun_prod {f : α -> β × γ} : Measurable f ↔ (Measurable fun a =>
 (f a).1) ∧ Measurable fun a => (f a).2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measurable_fun_prod {f : α → β × γ} :
    Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
  ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩

@[fun_prop]
/-
**measurable_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_swap : Measurable (Prod.swap : α × β -> β × α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
theorem measurable_swap : Measurable (Prod.swap : α × β → β × α) :=
  Measurable.prod measurable_snd measurable_fst
/-
**measurable_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_swap_iff {_ : MeasurableSpace γ} {f : α × β -> γ} : Measurable 
(f ∘ Prod.swap) ↔ Measurable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem measurable_swap_iff {_ : MeasurableSpace γ} {f : α × β → γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩

@[measurability]
/-
**MeasurableSet.prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {mβ : MeasurableSp
ace β} {s : Set α} {t : Set β},   MeasurableSet s → MeasurableSet t → Measurable
Set (s ×ˢ t)
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
protected theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)
/-
**measurableSet_prod_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonem
pty) : MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t
参数：h : (s ×ˢ t).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.mk_preimage_prod_left`：mk_preimage_prod_left (hb : b in t) : (fun a 
=> (a, b)) ⁻¹' s ×ˢ t = s
· 使用定理 `Set.mk_preimage_prod_right`：mk_preimage_prod_right (ha : a in s) : Prod.
mk a ⁻¹' s ×ˢ t = t
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t := by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prodMk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prodMk_left hst
  simp_all
/-
**measurableSet_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_prod {s : Set α} {t : Set β} : MeasurableSet (s ×ˢ t) ↔ Meas
urableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `measurableSet_prod_of_nonempty`：measurableSet_prod_of_nonempty {s : Set 
α} {t : Set β} (h : (s ×ˢ t).Nonempty) : MeasurableSet (s ×ˢ t) ↔ MeasurableSet 
s ∧ MeasurableSet t
· 使用定理 `Set.prod_nonempty_iff`：prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempt
y ∧ t.Nonempty
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]
/-
**measurableSet_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_swap_iff {s : Set (α × β)} : MeasurableSet (Prod.swap ⁻¹' s)
 ↔ MeasurableSet s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩
/-
**Prod.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instMeasurableSingletonClass [MeasurableSingletonClass α] [Measurable
SingletonClass β] : MeasurableSingletonClass (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
-/
instance Prod.instMeasurableSingletonClass
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩

/-- See `measurable_from_prod_countable_left` for a version where we assume that singletons are
measurable instead of reasoning about `measurableAtom`. -/
/-
**measurable_from_prod_countable_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_from_prod_countable_left' [Countable β] {f : α × β -> γ} (hf : 
forall y, Measurable fun x => f (x, y)) (h'f : forall y y' x, y' in measurableAt
om y -> f (x, y') = f (x, y)) : Measurable f
参数：hf : forall y, Measurable fun x => f (x, y)；h'f : forall y y' x, y' in measur
ableAtom y -> f (x, y') = f (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mem_measurableAtom_self`：∀ {β : Type u_2} [inst : MeasurableSpace β] (x 
: β), x ∈ measurableAtom x
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用引理 `MeasurableSet.measurableAtom_of_countable`：MeasurableSet.measurableAtom_
of_countable [Countable β] (x : β) : MeasurableSet (measurableAtom x)

--- 原说明 ---
See `measurable_from_prod_countable_left` for a version where we assume that sin
gletons are
measurable instead of reasoning about `measurableAtom`.
-/
theorem measurable_from_prod_countable_left' [Countable β] {f : α × β → γ}
    (hf : ∀ y, Measurable fun x => f (x, y))
    (h'f : ∀ y y' x, y' ∈ measurableAtom y → f (x, y') = f (x, y)) : Measurable f := fun s hs => by
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ (measurableAtom y : Set β) := by
    ext1 ⟨x, y⟩
    simp only [mem_preimage, mem_iUnion, mem_prod]
    refine ⟨fun h ↦ ⟨y, h, mem_measurableAtom_self y⟩, ?_⟩
    rintro ⟨y', hy's, hy'⟩
    rwa [h'f y' y x hy']
  rw [this]
  exact .iUnion (fun y ↦ (hf y hs).prod (.measurableAtom_of_countable y))

/-- See `measurable_from_prod_countable_right` for a version where we assume that singletons are
measurable instead of reasoning about `measurableAtom`. -/
/-
**measurable_from_prod_countable_right'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_from_prod_countable_right' [Countable α] {f : α × β -> γ} (hf :
 forall x, Measurable fun y => f (x, y)) (h'f : forall x x' y, x' in measurableA
tom x -> f (x', y) = f (x, y)) : Measurable f
参数：hf : forall x, Measurable fun y => f (x, y)；h'f : forall x x' y, x' in measur
ableAtom x -> f (x', y) = f (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_from_prod_countable_left'`：measurable_from_prod_countable_lef
t' [Countable β] {f : α × β -> γ} (hf : forall y, Measurable fun x => f (x, y)) 
(h'f : forall y y' x, y' i…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)

--- 原说明 ---
See `measurable_from_prod_countable_right` for a version where we assume that si
ngletons are
measurable instead of reasoning about `measurableAtom`.
-/
lemma measurable_from_prod_countable_right' [Countable α] {f : α × β → γ}
    (hf : ∀ x, Measurable fun y => f (x, y))
    (h'f : ∀ x x' y, x' ∈ measurableAtom x → f (x', y) = f (x, y)) : Measurable f := by
  change Measurable ((fun p ↦ f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable_left' hf h'f).comp measurable_swap

/-- For the version where the first space in the product is countable,
see `measurable_from_prod_countable_right`. -/
/-
**measurable_from_prod_countable_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_from_prod_countable_left [Countable β] [MeasurableSingletonClas
s β] {f : α × β -> γ} (hf : forall y, Measurable fun x => f (x, y)) : Measurable
 f
参数：hf : forall y, Measurable fun x => f (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_from_prod_countable_left'`：measurable_from_prod_countable_lef
t' [Countable β] {f : α × β -> γ} (hf : forall y, Measurable fun x => f (x, y)) 
(h'f : forall y y' x, y' i…
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
· 使用定理 `measurableAtom_of_measurableSingletonClass`：∀ {β : Type u_2} [inst : Mea
surableSpace β] [MeasurableSingletonClass β] (x : β), measurableAtom x = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
For the version where the first space in the product is countable,
see `measurable_from_prod_countable_right`.
-/
theorem measurable_from_prod_countable_left [Countable β] [MeasurableSingletonClass β]
    {f : α × β → γ} (hf : ∀ y, Measurable fun x => f (x, y)) :
    Measurable f :=
  measurable_from_prod_countable_left' hf (by simp +contextual)

/-- For the version where the second space in the product is countable,
see `measurable_from_prod_countable_left`. -/
/-
**measurable_from_prod_countable_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_from_prod_countable_right [Countable α] [MeasurableSingletonCla
ss α] {f : α × β -> γ} (hf : forall x, Measurable fun y => f (x, y)) : Measurabl
e f
参数：hf : forall x, Measurable fun y => f (x, y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `measurable_from_prod_countable_right'`：measurable_from_prod_countable_ri
ght' [Countable α] {f : α × β -> γ} (hf : forall x, Measurable fun y => f (x, y)
) (h'f : forall x x' y, x' …
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
· 使用定理 `measurableAtom_of_measurableSingletonClass`：∀ {β : Type u_2} [inst : Mea
surableSpace β] [MeasurableSingletonClass β] (x : β), measurableAtom x = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
For the version where the second space in the product is countable,
see `measurable_from_prod_countable_left`.
-/
lemma measurable_from_prod_countable_right [Countable α] [MeasurableSingletonClass α]
    {f : α × β → γ} (hf : ∀ x, Measurable fun y => f (x, y)) : Measurable f :=
  measurable_from_prod_countable_right' hf (by simp +contextual)

/-- A piecewise function on countably many pieces is measurable if all the data is measurable. -/
/-
**Measurable.find** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.find {_ : MeasurableSpace α} {f : Nat -> α -> β} {p : Nat -> α 
-> Prop} [forall n, DecidablePred (p n)] (hf : forall n, Measurable (f n)) (hp :
 forall n, MeasurableSet { x | p n x }) (h : forall x, exists n, p n x) : Measur
able fun x => f (Nat.find (h x)) x
参数：p n；hf : forall n, Measurable (f n)；hp : forall n, MeasurableSet { x | p n x 
}；h : forall x, exists n, p n x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_from_prod_countable_left`：measurable_from_prod_countable_left
 [Countable β] [MeasurableSingletonClass β] {f : α × β -> γ} (hf : forall y, Mea
surable fun x => f (x, y)…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `measurable_find`：measurable_find {p : α -> Nat -> Prop} [forall x, Decid
ablePred (p x)] (hp : forall x, exists N, p x N) (hm : forall k, MeasurableSet {
 x | …

--- 原说明 ---
A piecewise function on countably many pieces is measurable if all the data is m
easurable.
-/
theorem Measurable.find {_ : MeasurableSpace α} {f : ℕ → α → β} {p : ℕ → α → Prop}
    [∀ n, DecidablePred (p n)] (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet { x | p n x })
    (h : ∀ x, ∃ n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  have : Measurable fun p : α × ℕ => f p.2 p.1 := measurable_from_prod_countable_left fun n => hf n
  this.comp (Measurable.prodMk measurable_id (measurable_find h hp))

/-- Let `t i` be a countable covering of a set `T` by measurable sets. Let `f i : t i → β` be a
family of functions that agree on the intersections `t i ∩ t j`. Then the function
`Set.iUnionLift t f _ _ : T → β`, defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable. -/
/-
**measurable_iUnionLift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_iUnionLift [Countable ι] {t : ι -> Set α} {f : forall i, t i ->
 β} (htf : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), f i ⟨x, hxi⟩ 
= f j ⟨x, hxj⟩) {T : Set α} (hT : T subseteq ⋃ i, t i) (htm : forall i, Measurab
leSet (t i)) (hfm : forall i, Measurable (f i)) : Measurable (iUnionLift t f htf
 T hT)
参数：htf : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), f i ⟨x, hxi⟩ = 
f j ⟨x, hxj⟩；hT : T subseteq ⋃ i, t i；htm : forall i, MeasurableSet (t i)；hfm : 
forall i, Measurable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_iUnionLift`：preimage_iUnionLift (t : Set β) : iUnionLift S 
f hf T hT ⁻¹' t = inclusion hT ⁻¹' (⋃ i, inclusion (subset_iUnion S i) '' f i ⁻¹
' t)
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.image_inclusion`：MeasurableSet.image_inclusion {s t : Set 
α} (h : s subseteq t) {u : Set s} (hs : MeasurableSet s) (hu : MeasurableSet u) 
: MeasurableSet (in…
· 使用定理 `measurable_inclusion`：measurable_inclusion {s t : Set α} (h : s subseteq
 t) : Measurable (inclusion h)

--- 原说明 ---
Let `t i` be a countable covering of a set `T` by measurable sets. Let `f i : t 
i → β` be a
family of functions that agree on the intersections `t i ∩ t j`. Then the functi
on
`Set.iUnionLift t f _ _ : T → β`, defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, i
s measurable.
-/
theorem measurable_iUnionLift [Countable ι] {t : ι → Set α} {f : ∀ i, t i → β}
    (htf : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    {T : Set α} (hT : T ⊆ ⋃ i, t i) (htm : ∀ i, MeasurableSet (t i)) (hfm : ∀ i, Measurable (f i)) :
    Measurable (iUnionLift t f htf T hT) := fun s hs => by
  rw [preimage_iUnionLift]
  exact .preimage (.iUnion fun i => .image_inclusion _ (htm _) (hfm i hs)) (measurable_inclusion _)

/-- Let `t i` be a countable covering of `α` by measurable sets. Let `f i : t i → β` be a family of
functions that agree on the intersections `t i ∩ t j`. Then the function `Set.liftCover t f _ _`,
defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable. -/
/-
**measurable_liftCover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_liftCover [Countable ι] (t : ι -> Set α) (htm : forall i, Measu
rableSet (t i)) (f : forall i, t i -> β) (hfm : forall i, Measurable (f i)) (hf 
: forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), f i ⟨x, hxi⟩ = f j ⟨x,
 hxj⟩) (htU : ⋃ i, t i = univ) : Measurable (liftCover t f hf htU)
参数：t : ι -> Set α；htm : forall i, MeasurableSet (t i)；f : forall i, t i -> β；hfm
 : forall i, Measurable (f i)；hf : forall (i j) (x : α) (hxi : x in t i) (hxj : 
x in t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩；htU : ⋃ i, t i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_liftCover`：preimage_liftCover (t : Set β) : liftCover S f h
f hS ⁻¹' t = ⋃ i, (↑) '' f i ⁻¹' t
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)

--- 原说明 ---
Let `t i` be a countable covering of `α` by measurable sets. Let `f i : t i → β`
 be a family of
functions that agree on the intersections `t i ∩ t j`. Then the function `Set.li
ftCover t f _ _`,
defined as `f i ⟨x, hx⟩` for `hx : x ∈ t i`, is measurable.
-/
theorem measurable_liftCover [Countable ι] (t : ι → Set α) (htm : ∀ i, MeasurableSet (t i))
    (f : ∀ i, t i → β) (hfm : ∀ i, Measurable (f i))
    (hf : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (htU : ⋃ i, t i = univ) :
    Measurable (liftCover t f hf htU) := fun s hs => by
  rw [preimage_liftCover]
  exact .iUnion fun i => .subtype_image (htm i) <| hfm i hs

/-- Let `t i` be a nonempty countable family of measurable sets in `α`. Let `g i : α → β` be a
family of measurable functions such that `g i` agrees with `g j` on `t i ∩ t j`. Then there exists
a measurable function `f : α → β` that agrees with each `g i` on `t i`.

We only need the assumption `[Nonempty ι]` to prove `[Nonempty (α → β)]`. -/
/-
**exists_measurable_piecewise** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_measurable_piecewise {ι} [Countable ι] [Nonempty ι] (t : ι -> Set α
) (t_meas : forall n, MeasurableSet (t n)) (g : ι -> α -> β) (hg : forall n, Mea
surable (g n)) (ht : Pairwise fun i j => EqOn (g i) (g j) (t i inter t j)) : exi
sts f : α -> β, Measurable f ∧ forall n, EqOn f (g n) (t n)
参数：t : ι -> Set α；t_meas : forall n, MeasurableSet (t n)；g : ι -> α -> β；hg : fo
rall n, Measurable (g n)；ht : Pairwise fun i j => EqOn (g i) (g j) (t i inter t 
j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `measurable_iUnionLift`：measurable_iUnionLift [Countable ι] {t : ι -> Set
 α} {f : forall i, t i -> β} (htf : forall (i j) (x : α) (hxi : x in t i) (hxj :
 x in t j),…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `Measurable.dite`：Measurable.dite [forall x, Decidable (x in s)] {f : s -
> β} (hf : Measurable f) {g : (sᶜ : Set α) -> β} (hg : Measurable g) (hs : Measu
rable…
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩

--- 原说明 ---
Let `t i` be a nonempty countable family of measurable sets in `α`. Let `g i : α
 → β` be a
family of measurable functions such that `g i` agrees with `g j` on `t i ∩ t j`.
 Then there exists
a measurable function `f : α → β` that agrees with each `g i` on `t i`.

We only need the assumption `[Nonempty ι]` to prove `[Nonempty (α → β)]`.
-/
theorem exists_measurable_piecewise {ι} [Countable ι] [Nonempty ι] (t : ι → Set α)
    (t_meas : ∀ n, MeasurableSet (t n)) (g : ι → α → β) (hg : ∀ n, Measurable (g n))
    (ht : Pairwise fun i j => EqOn (g i) (g j) (t i ∩ t j)) :
    ∃ f : α → β, Measurable f ∧ ∀ n, EqOn f (g n) (t n) := by
  inhabit ι
  set g' : (i : ι) → t i → β := fun i => g i ∘ (↑)
  -- see https://github.com/leanprover-community/mathlib4/issues/2184
  have ht' : ∀ (i j) (x : α) (hxi : x ∈ t i) (hxj : x ∈ t j), g' i ⟨x, hxi⟩ = g' j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exact ht hij ⟨hxi, hxj⟩
  set f : (⋃ i, t i) → β := iUnionLift t g' ht' _ Subset.rfl
  have hfm : Measurable f := measurable_iUnionLift _ _ t_meas
    (fun i => (hg i).comp measurable_subtype_coe)
  classical
    refine ⟨fun x => if hx : x ∈ ⋃ i, t i then f ⟨x, hx⟩ else g default x,
      hfm.dite ((hg default).comp measurable_subtype_coe) (.iUnion t_meas), fun i x hx => ?_⟩
    simp only [dif_pos (mem_iUnion.2 ⟨i, hx⟩)]
    exact iUnionLift_of_mem ⟨x, mem_iUnion.2 ⟨i, hx⟩⟩ hx

end Prod

section Pi

variable {X : δ → Type*} [MeasurableSpace α]

/-
**MeasurableSpace.pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MeasurableSpace.pi [m : forall a, MeasurableSpace (X a)] : MeasurableSpace
 (forall a, X a)
参数：X a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (X a)] : MeasurableSpace (∀ a, X a) :=
  ⨆ a, (m a).comap fun b => b a

variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]
/-
**measurable_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_pi_iff {g : α -> forall a, X a} : Measurable g ↔ forall a, Meas
urable fun x => g x a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSpace.comap_iSup`：comap_iSup {m : ι -> MeasurableSpace α} : (⨆
 i, m i).comap g = ⨆ i, (m i).comap g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measurable_pi_iff {g : α → ∀ a, X a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
/-
**measurable_pi_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_pi_apply (a : δ) : Measurable fun f : forall a, X a => f a
参数：a : δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=
  measurable_pi_iff.1 measurable_id a
/-
**MeasurableSpace.comap_le_comap_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSpace.comap_le_comap_pi {g : (a : δ) -> β -> X a} (a : δ) : .com
ap (g a) inferInstance <= pi.comap (fun b c => g c b)
参数：a : δ；a : δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.comap_iSup`：comap_iSup {m : ι -> MeasurableSpace α} : (⨆
 i, m i).comap g = ⨆ i, (m i).comap g
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem MeasurableSpace.comap_le_comap_pi {g : (a : δ) → β → X a} (a : δ) :
    .comap (g a) inferInstance ≤ pi.comap (fun b c ↦ g c b) := by
  simpa only [pi, comap_iSup] using le_iSup_of_le a <| by measurability
/-
**Measurable.eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : Measurable g) : Mea
surable fun x => g x a
参数：hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop]
/-
**measurable_pi_lambda** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_pi_lambda (f : α -> forall a, X a) (hf : forall a, Measurable f
un c => f c a) : Measurable f
参数：f : α -> forall a, X a；hf : forall a, Measurable fun c => f c a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
-/
theorem measurable_pi_lambda (f : α → ∀ a, X a) (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf
/-
**MeasurableSpace.comap_process_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSpace.comap_process_pi (X : (a : δ) -> β -> X a) : MeasurableSpa
ce.comap (fun b a => X a b) inferInstance = ⨆ a, MeasurableSpace.comap (X a) inf
erInstance
参数：X : (a : δ) -> β -> X a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.comap_iSup`：comap_iSup {m : ι -> MeasurableSpace α} : (⨆
 i, m i).comap g = ⨆ i, (m i).comap g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSpace.comap_comp`：comap_comp {f : β -> α} {g : γ -> β} : (m.co
map f).comap g = m.comap (f ∘ g)
-/
lemma MeasurableSpace.comap_process_pi (X : (a : δ) → β → X a) :
    MeasurableSpace.comap (fun b a ↦ X a b) inferInstance =
      ⨆ a, MeasurableSpace.comap (X a) inferInstance := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable. -/
@[fun_prop]
/-
**measurable_update'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_update' {a : δ} [DecidableEq δ] : Measurable (fun p : (forall i
, X i) × X a => update p.1 a p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)

--- 原说明 ---
The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable
.
-/
theorem measurable_update' {a : δ} [DecidableEq δ] :
    Measurable (fun p : (∀ i, X i) × X a ↦ update p.1 a p.2) := by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

@[fun_prop]
/-
**measurable_uniqueElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_uniqueElim [Unique δ] : Measurable (uniqueElim : X (default : δ
) -> forall i, X i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem measurable_uniqueElim [Unique δ] :
    Measurable (uniqueElim : X (default : δ) → ∀ i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

@[fun_prop]
/-
**measurable_updateFinset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_updateFinset' [DecidableEq δ] {s : Finset δ} : Measurable (fun 
p : (Π i, X i) × (Π i : s, X i) => updateFinset p.1 s p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem measurable_updateFinset' [DecidableEq δ] {s : Finset δ} :
    Measurable (fun p : (Π i, X i) × (Π i : s, X i) ↦ updateFinset p.1 s p.2) := by
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, Measurable.eval, measurable_fst, measurable_snd]

@[fun_prop]
/-
**measurable_updateFinset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_updateFinset [DecidableEq δ] {s : Finset δ} {x : Π i, X i} : Me
asurable (updateFinset x s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_updateFinset'`：measurable_updateFinset' [DecidableEq δ] {s : 
Finset δ} : Measurable (fun p : (Π i, X i) × (Π i : s, X i) => updateFinset p.1 
s p.2)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
theorem measurable_updateFinset [DecidableEq δ] {s : Finset δ} {x : Π i, X i} :
    Measurable (updateFinset x s) :=
  measurable_updateFinset'.comp measurable_prodMk_left

@[fun_prop]
/-
**measurable_updateFinset_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_updateFinset_left [DecidableEq δ] {s : Finset δ} {x : Π i : s, 
X i} : Measurable (updateFinset · s x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_updateFinset'`：measurable_updateFinset' [DecidableEq δ] {s : 
Finset δ} : Measurable (fun p : (Π i, X i) × (Π i : s, X i) => updateFinset p.1 
s p.2)
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem measurable_updateFinset_left [DecidableEq δ] {s : Finset δ} {x : Π i : s, X i} :
    Measurable (updateFinset · s x) :=
  measurable_updateFinset'.comp measurable_prodMk_right

/-- The function `update f a : X a → Π a, X a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[fun_prop]
/-
**measurable_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_update (f : forall a : δ, X a) {a : δ} [DecidableEq δ] : Measur
able (update f a)
参数：f : forall a : δ, X a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_update'`：measurable_update' {a : δ} [DecidableEq δ] : Measura
ble (fun p : (forall i, X i) × X a => update p.1 a p.2)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)

--- 原说明 ---
The function `update f a : X a → Π a, X a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurab
le.
-/
theorem measurable_update (f : ∀ a : δ, X a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  measurable_update'.comp measurable_prodMk_left

@[fun_prop]
/-
**measurable_update_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_update_left {a : δ} [DecidableEq δ] {x : X a} : Measurable (upd
ate · a x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_update'`：measurable_update' {a : δ} [DecidableEq δ] : Measura
ble (fun p : (forall i, X i) × X a => update p.1 a p.2)
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem measurable_update_left {a : δ} [DecidableEq δ] {x : X a} :
    Measurable (update · a x) :=
  measurable_update'.comp measurable_prodMk_right

@[fun_prop]
/-
**Set.measurable_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.measurable_restrict (s : Set δ) : Measurable (s.domRestrict (π
参数：s : Set δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Set.measurable_restrict (s : Set δ) : Measurable (s.domRestrict (π := X)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[fun_prop]
/-
**Set.measurable_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.measurable_restrict (s : Set δ) : Measurable (s.domRestrict (π
参数：s : Set δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Set.measurable_restrict₂ {s t : Set δ} (hst : s ⊆ t) :
    Measurable (domRestrict₂ (π := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[fun_prop]
/-
**Finset.measurable_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π
参数：s : Finset δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π := X)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[fun_prop]
/-
**Finset.measurable_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π
参数：s : Finset δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Finset.measurable_restrict₂ {s t : Finset δ} (hst : s ⊆ t) :
    Measurable (Finset.restrict₂ (π := X) hst) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[fun_prop]
/-
**Set.measurable_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.measurable_restrict_apply (s : Set α) {f : α -> γ} (hf : Measurable f)
 : Measurable (s.domRestrict f)
参数：s : Set α；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem Set.measurable_restrict_apply (s : Set α) {f : α → γ} (hf : Measurable f) :
    Measurable (s.domRestrict f) := hf.comp measurable_subtype_coe

@[fun_prop]
/-
**Set.measurable_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.measurable_restrict (s : Set δ) : Measurable (s.domRestrict (π
参数：s : Set δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Set.measurable_restrict₂_apply {s t : Set α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (domRestrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

@[fun_prop]
/-
**Finset.measurable_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_restrict_apply (s : Finset α) {f : α -> γ} (hf : Measura
ble f) : Measurable (s.restrict f)
参数：s : Finset α；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
-/
theorem Finset.measurable_restrict_apply (s : Finset α) {f : α → γ} (hf : Measurable f) :
    Measurable (s.restrict f) := hf.comp measurable_subtype_coe

@[fun_prop]
/-
**Finset.measurable_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π
参数：s : Finset δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem Finset.measurable_restrict₂_apply {s t : Finset α} (hst : s ⊆ t)
    {f : t → γ} (hf : Measurable f) :
    Measurable (restrict₂ (π := fun _ ↦ γ) hst f) := hf.comp (measurable_inclusion hst)

variable (X) in
/-
**measurable_eq_mp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_eq_mp {i i' : δ} (h : i = i') : Measurable (congr_arg X h).mp
参数：h : i = i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem measurable_eq_mp {i i' : δ} (h : i = i') : Measurable (congr_arg X h).mp := by
  cases h
  exact measurable_id

variable (X) in
/-
**Measurable.eq_mp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.eq_mp {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β ->
 X i} (hf : Measurable f) : Measurable fun x => (congr_arg X h).mp (f x)
参数：h : i = i'；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `measurable_eq_mp`：measurable_eq_mp {i i' : δ} (h : i = i') : Measurable 
(congr_arg X h).mp
-/
theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β → X i}
    (hf : Measurable f) : Measurable fun x => (congr_arg X h).mp (f x) :=
  (measurable_eq_mp X h).comp hf

@[fun_prop]
/-
**measurable_piCongrLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_piCongrLeft (f : δ' ≃ δ) : Measurable (Equiv.piCongrLeft X f)
参数：f : δ' ≃ δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Equiv.piCongrLeft_apply_eq_cast`：piCongrLeft_apply_eq_cast {P : β -> Sor
t v} {e : α ≃ β} (f : (a : α) -> P (e a)) (b : β) : piCongrLeft P e f b = cast (
congr_arg P (e.apply_…
· 使用定理 `Measurable.eq_mp`：Measurable.eq_mp {β} [MeasurableSpace β] {i i' : δ} (h
 : i = i') {f : β -> X i} (hf : Measurable f) : Measurable fun x => (congr_arg X
 h).mp…
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem measurable_piCongrLeft (f : δ' ≃ δ) : Measurable (Equiv.piCongrLeft X f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [Equiv.piCongrLeft_apply_eq_cast]
  exact Measurable.eq_mp X (f.apply_symm_apply i) <| measurable_pi_apply <| f.symm i

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
lemmas, like `MeasurableSet.prod`. -/
@[measurability]
/-
**MeasurableSet.pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → MeasurableSpace (X a
)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀ i ∈ s, MeasurableSe
t (t i)) → MeasurableSet (s.pi t)
参数：a : δ；X a；i : δ；X i；∀ i ∈ s, MeasurableSet (t i)；s.pi t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_def`：pi_def (i : Set α) (s : forall a, Set (π a)) : pi i s = ⋂ a 
in i, eval a ⁻¹' s a
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a

--- 原说明 ---
Even though we cannot use projection notation, we still keep a dot to be consist
ent with similar
lemmas, like `MeasurableSet.prod`.
-/
protected theorem MeasurableSet.pi {s : Set δ} {t : ∀ i : δ, Set (X i)} (hs : s.Countable)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (s.pi t) := by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)
/-
**MeasurableSet.univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → MeasurableSpace (X a
)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ), MeasurableSet (t i)) →
 MeasurableSet (Set.univ.pi t)
参数：a : δ；X a；i : δ；X i；∀ (i : δ), MeasurableSet (t i)；Set.univ.pi t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
protected theorem MeasurableSet.univ_pi [Countable δ] {t : ∀ i : δ, Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i
/-
**MeasurableSet.univ_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.univ_pi' [Countable δ] {t : forall i : δ, Set (X i)} (ht : f
orall i, MeasurableSet (t i)) : MeasurableSet {f : forall i : δ, X i | forall i 
: δ, f i in t i}
参数：X i；ht : forall i, MeasurableSet (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.congr`：MeasurableSet.congr {s t : Set α} (hs : MeasurableS
et s) (h : s = t) : MeasurableSet t
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
-/
theorem MeasurableSet.univ_pi' [Countable δ] {t : ∀ i : δ, Set (X i)}
    (ht : ∀ i, MeasurableSet (t i)) : MeasurableSet {f : ∀ i : δ, X i | ∀ i : δ, f i ∈ t i} :=
  (MeasurableSet.univ_pi ht).congr (by grind)
/-
**measurableSet_pi_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_pi_of_nonempty {s : Set δ} {t : forall i, Set (X i)} (hs : s
.Countable) (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ forall i in s, Me
asurableSet (t i)
参数：X i；hs : s.Countable；h : (pi s t).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.update_preimage_pi`：update_preimage_pi [DecidableEq ι] {f : forall i
, α i} (hi : i in s) (hf : forall j in s, j != i -> f j in t j) : update f i ⁻¹'
 s.pi t = t …
· 使用定理 `measurable_update`：measurable_update (f : forall a : δ, X a) {a : δ} [De
cidableEq δ] : Measurable (update f a)
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
-/
theorem measurableSet_pi_of_nonempty {s : Set δ} {t : ∀ i, Set (X i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ ∀ i ∈ s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert! measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj
/-
**measurableSet_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_pi {s : Set δ} {t : forall i, Set (X i)} (hs : s.Countable) 
: MeasurableSet (pi s t) ↔ (forall i in s, MeasurableSet (t i)) ∨ pi s t = ∅
参数：X i；hs : s.Countable。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `measurableSet_pi_of_nonempty`：measurableSet_pi_of_nonempty {s : Set δ} {
t : forall i, Set (X i)} (hs : s.Countable) (h : (pi s t).Nonempty) : Measurable
Set (pi s t) ↔ for…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem measurableSet_pi {s : Set δ} {t : ∀ i, Set (X i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (∀ i ∈ s, MeasurableSet (t i)) ∨ pi s t = ∅ := by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]
/-
**Pi.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instMeasurableSingletonClass [Countable δ] [forall a, MeasurableSinglet
onClass (X a)] : MeasurableSingletonClass (forall a, X a)
参数：X a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `Set.univ_pi_singleton`：univ_pi_singleton (f : forall i, α i) : (pi univ 
fun i => {f i}) = ({f} : Set (forall i, α i))
-/
instance Pi.instMeasurableSingletonClass [Countable δ] [∀ a, MeasurableSingletonClass (X a)] :
    MeasurableSingletonClass (∀ a, X a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

variable (X)

@[fun_prop]
/-
**measurable_piEquivPiSubtypeProd_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_piEquivPiSubtypeProd_symm (p : δ -> Prop) [DecidablePred p] : M
easurable (Equiv.piEquivPiSubtypeProd p X).symm
参数：p : δ -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.piEquivPiSubtypeProd_symm_apply`：∀ {α : Type u_9} (p : α → Prop) (
β : α → Type u_10) [inst : DecidablePred p]   (f : ((i : { x // p x }) → β ↑i) ×
 ((i : { x // ¬p x }) → β ↑…
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem measurable_piEquivPiSubtypeProd_symm (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X).symm := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : ∀ i : { x // p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg, not_false_iff]
    have : Measurable fun (f : ∀ i : { x // ¬p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // ¬p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_snd

@[fun_prop]
/-
**measurable_piEquivPiSubtypeProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_piEquivPiSubtypeProd (p : δ -> Prop) [DecidablePred p] : Measur
able (Equiv.piEquivPiSubtypeProd p X)
参数：p : δ -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem measurable_piEquivPiSubtypeProd (p : δ → Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X) :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

end Pi

/-
**TProd.instMeasurableSpace** 是 Mathlib 中的一个定义，位于命名空间 `TProd`。
形式化陈述：{δ : Type u_4} →   (X : δ → Type u_6) → [(i : δ) → MeasurableSpace (X i)] 
→ (l : List δ) → MeasurableSpace (List.TProd X l)
参数：X : δ → Type u_6；i : δ；X i；l : List δ；List.TProd X l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TProd.instMeasurableSpace (X : δ → Type*) [∀ i, MeasurableSpace (X i)] :
    ∀ l : List δ, MeasurableSpace (List.TProd X l)
  | [] => PUnit.instMeasurableSpace
  | _::is => @Prod.instMeasurableSpace _ _ _ (TProd.instMeasurableSpace X is)

section TProd

open List

variable {X : δ → Type*} [∀ i, MeasurableSpace (X i)]

/-
**measurable_tProd_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ X l)
参数：l : List δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ X l) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).prodMk ih

set_option backward.isDefEq.respectTransparency false in
/-
**measurable_tProd_elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (i : δ) → MeasurableSpace (X i
)] [inst_1 : DecidableEq δ] {l : List δ}   {i : δ} (hi : i ∈ l), Measurable fun 
v => v.elim hi
参数：i : δ；X i；hi : i ∈ l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_tProd_elim [DecidableEq δ] :
    ∀ {l : List δ} {i : δ} (hi : i ∈ l), Measurable fun v : TProd X l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simp only [TProd.elim_of_ne _ hji]
      rw [mem_cons] at hj
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd
/-
**measurable_tProd_elim'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : forall i, i in l)
 : Measurable (TProd.elim' h : TProd X l -> forall i, X i)
参数：h : forall i, i in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_tProd_elim`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (i : 
δ) → MeasurableSpace (X i)] [inst_1 : DecidableEq δ] {l : List δ}   {i : δ} (hi 
: i ∈ l), M…
-/
theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : ∀ i, i ∈ l) :
    Measurable (TProd.elim' h : TProd X l → ∀ i, X i) :=
  measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)
/-
**MeasurableSet.tProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.tProd (l : List δ) {s : forall i, Set (X i)} (hs : forall i,
 MeasurableSet (s i)) : MeasurableSet (Set.tprod l s)
参数：l : List δ；X i；hs : forall i, MeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
-/
theorem MeasurableSet.tProd (l : List δ) {s : ∀ i, Set (X i)} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction l with
  | nil => exact MeasurableSet.univ
  | cons i l ih => exact (hs i).prod ih

end TProd

/-
**Sum.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpa
ce β] : MeasurableSpace (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sum.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α ⊕ β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr

section Sum

@[fun_prop]
/-
**measurable_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_inl [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.
inl α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_le_map`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSp
ace α} {m₂ : MeasurableSpace β} {f : α → β},   m₂ ≤ MeasurableSpace.map f m₁ → M
easurable …
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem measurable_inl [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inl α β) :=
  Measurable.of_le_map inf_le_left

@[fun_prop]
/-
**measurable_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_inr [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.
inr α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_le_map`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSp
ace α} {m₂ : MeasurableSpace β} {f : α → β},   m₂ ≤ MeasurableSpace.map f m₁ → M
easurable …
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem measurable_inr [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inr α β) :=
  Measurable.of_le_map inf_le_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}
/-
**measurableSet_sum_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_sum_iff {s : Set (α oplus β)} : MeasurableSet s ↔ Measurable
Set (Sum.inl ⁻¹' s) ∧ MeasurableSet (Sum.inr ⁻¹' s)
参数：α oplus β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_sum_iff {s : Set (α ⊕ β)} :
    MeasurableSet s ↔ MeasurableSet (Sum.inl ⁻¹' s) ∧ MeasurableSet (Sum.inr ⁻¹' s) :=
  Iff.rfl
/-
**measurable_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fun_sum {_ : MeasurableSpace γ} {f : α oplus β -> γ} (hl : Meas
urable (f ∘ Sum.inl)) (hr : Measurable (f ∘ Sum.inr)) : Measurable f
参数：hl : Measurable (f ∘ Sum.inl)；hr : Measurable (f ∘ Sum.inr)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSpace.comap_le_iff_le_map`：comap_le_iff_le_map {f : α -> β} : 
m'.comap f <= m ↔ m' <= m.map f
-/
theorem measurable_fun_sum {_ : MeasurableSpace γ} {f : α ⊕ β → γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
  Measurable.of_comap_le <|
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)

@[fun_prop]
/-
**Measurable.sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.sumElim {_ : MeasurableSpace γ} {f : α -> γ} {g : β -> γ} (hf :
 Measurable f) (hg : Measurable g) : Measurable (Sum.elim f g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fun_sum`：measurable_fun_sum {_ : MeasurableSpace γ} {f : α op
lus β -> γ} (hl : Measurable (f ∘ Sum.inl)) (hr : Measurable (f ∘ Sum.inr)) : Me
asurable…
-/
theorem Measurable.sumElim {_ : MeasurableSpace γ} {f : α → γ} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_fun_sum hf hg
/-
**Measurable.sumMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.sumMap {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α -
> β} {g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.map 
f g)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.sumElim`：Measurable.sumElim {_ : MeasurableSpace γ} {f : α ->
 γ} {g : β -> γ} (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.elim 
f g)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_inl`：measurable_inl [MeasurableSpace α] [MeasurableSpace β] :
 Measurable (@Sum.inl α β)
· 使用定理 `measurable_inr`：measurable_inr [MeasurableSpace α] [MeasurableSpace β] :
 Measurable (@Sum.inr α β)
-/
theorem Measurable.sumMap {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.map f g) :=
  (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)
/-
**measurableSet_inl_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {mβ : MeasurableSp
ace β} {s : Set α},   MeasurableSet (Sum.inl '' s) ↔ MeasurableSet s
参数：Sum.inl '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Set.preimage_inr_image_inl`：preimage_inr_image_inl (s : Set α) : Sum.inr
 ⁻¹' @Sum.inl α β '' s = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem measurableSet_inl_image {s : Set α} :
    MeasurableSet (Sum.inl '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image
/-
**measurableSet_inr_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {mβ : MeasurableSp
ace β} {s : Set β},   MeasurableSet (Sum.inr '' s) ↔ MeasurableSet s
参数：Sum.inr '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.preimage_inl_image_inr`：preimage_inl_image_inr (s : Set β) : Sum.inl
 ⁻¹' @Sum.inr α β '' s = ∅
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem measurableSet_inr_image {s : Set β} :
    MeasurableSet (Sum.inr '' s : Set (α ⊕ β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image
/-
**measurableSet_range_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_range_inl [MeasurableSpace α] : MeasurableSet (range Sum.inl
 : Set (α oplus β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `MeasurableSet.inl_image`：∀ {α : Type u_1} {β : Type u_2} {m : Measurable
Space α} {mβ : MeasurableSpace β} {s : Set α},   MeasurableSet s → MeasurableSet
 (Sum.inl '' …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem measurableSet_range_inl [MeasurableSpace α] :
    MeasurableSet (range Sum.inl : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image
/-
**measurableSet_range_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_range_inr [MeasurableSpace α] : MeasurableSet (range Sum.inr
 : Set (α oplus β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `MeasurableSet.inr_image`：∀ {α : Type u_1} {β : Type u_2} {m : Measurable
Space α} {mβ : MeasurableSpace β} {s : Set β},   MeasurableSet s → MeasurableSet
 (Sum.inr '' …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem measurableSet_range_inr [MeasurableSpace α] :
    MeasurableSet (range Sum.inr : Set (α ⊕ β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image

end Sum

/-
**Sigma.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sigma.instMeasurableSpace {α} {β : α -> Type*} [m : forall a, MeasurableSp
ace (β a)] : MeasurableSpace (Sigma β)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sigma.instMeasurableSpace {α} {β : α → Type*} [m : ∀ a, MeasurableSpace (β a)] :
    MeasurableSpace (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)

section prop
variable [MeasurableSpace α] {p q : α → Prop}

/-
**measurableSet_setOfPred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → Prop}, MeasurableSet 
{a | p a} ↔ Measurable p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_prop`：measurable_to_prop {f : α -> Prop} (h : MeasurableSe
t (f ⁻¹' {True})) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_singleton_true`：∀ {α : Type u_1} (p : α → Prop), p ⁻¹' {Tru
e} = {a | p a}
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
@[simp] theorem measurableSet_setOfPred : MeasurableSet {a | p a} ↔ Measurable p :=
  ⟨fun h ↦ measurable_to_prop <| by simpa only [preimage_singleton_true], fun h => by
    simpa using h (measurableSet_singleton True)⟩

@[deprecated (since := "2026-07-09")] alias measurableSet_setOf := measurableSet_setOfPred
/-
**measurable_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {s : Set α} [inst : MeasurableSpace α], (Measurable fun x
 => x ∈ s) ↔ MeasurableSet s
参数：Measurable fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
-/
@[simp] theorem measurable_mem : Measurable (· ∈ s) ↔ MeasurableSet s :=
  measurableSet_setOfPred.symm

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOfPred

@[fun_prop]
alias ⟨_, MeasurableSet.mem⟩ := measurable_mem

@[fun_prop]
/-
**Measurable.not** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.not (hp : Measurable p) : Measurable (¬ p ·)
参数：hp : Measurable p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.not (hp : Measurable p) : Measurable (¬ p ·) :=
  measurableSet_setOfPred.1 hp.setOf.compl

@[fun_prop]
/-
**Measurable.and** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.and (hp : Measurable p) (hq : Measurable q) : Measurable fun a 
=> p a ∧ q a
参数：hp : Measurable p；hq : Measurable q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.and (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ∧ q a :=
  measurableSet_setOfPred.1 <| hp.setOf.inter hq.setOf

@[fun_prop]
/-
**Measurable.or** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.or (hp : Measurable p) (hq : Measurable q) : Measurable fun a =
> p a ∨ q a
参数：hp : Measurable p；hq : Measurable q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.or (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ∨ q a :=
  measurableSet_setOfPred.1 <| hp.setOf.union hq.setOf

@[fun_prop]
/-
**Measurable.imp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.imp (hp : Measurable p) (hq : Measurable q) : Measurable fun a 
=> p a -> q a
参数：hp : Measurable p；hq : Measurable q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `MeasurableSet.himp`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ⇨ s₂)
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.imp (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a → q a :=
  measurableSet_setOfPred.1 <| hp.setOf.himp hq.setOf

@[fun_prop]
/-
**Measurable.iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.iff (hp : Measurable p) (hq : Measurable q) : Measurable fun a 
=> p a ↔ q a
参数：hp : Measurable p；hq : Measurable q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.bihimp`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : 
Set α},   MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (bihimp s₁ s₂)
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.iff (hp : Measurable p) (hq : Measurable q) : Measurable fun a ↦ p a ↔ q a :=
  measurableSet_setOfPred.1 <| by
    simp_rw [iff_iff_implies_and_implies]; exact hq.setOf.bihimp hp.setOf

@[fun_prop]
/-
**Measurable.forall** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.forall [Countable ι] {p : ι -> α -> Prop} (hp : forall i, Measu
rable (p i)) : Measurable fun a => forall i, p i a
参数：hp : forall i, Measurable (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.forall [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
    Measurable fun a ↦ ∀ i, p i a :=
  measurableSet_setOfPred.1 <| by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i ↦ (hp i).setOf

@[fun_prop]
/-
**Measurable.exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.exists [Countable ι] {p : ι -> α -> Prop} (hp : forall i, Measu
rable (p i)) : Measurable fun a => exists i, p i a
参数：hp : forall i, Measurable (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Measurable.setOf`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p : α → P
rop}, Measurable p → MeasurableSet {a | p a}
-/
lemma Measurable.exists [Countable ι] {p : ι → α → Prop} (hp : ∀ i, Measurable (p i)) :
    Measurable fun a ↦ ∃ i, p i a :=
  measurableSet_setOfPred.1 <| by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun i ↦ (hp i).setOf

end prop

@[fun_prop]
/-
**Measurable.eq_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.eq_const {_ : MeasurableSpace α} [MeasurableSpace β] [Measurabl
eSingletonClass β] {f : α -> β} (hf : Measurable f) (a : β) : Measurable fun x =
> f x = a
参数：hf : Measurable f；a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `measurableSet_eq`：measurableSet_eq {a : α} : MeasurableSet { x | x = a }
-/
lemma Measurable.eq_const {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (a : β) : Measurable fun x => f x = a :=
  measurableSet_setOfPred.mp (measurableSet_eq.preimage hf)

@[fun_prop]
/-
**Measurable.const_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Measurable.const_eq {_ : MeasurableSpace α} [MeasurableSpace β] [Measurabl
eSingletonClass β] {f : α -> β} (hf : Measurable f) (a : β) : Measurable fun x =
> a = f x
参数：hf : Measurable f；a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Measurable.eq_const`：Measurable.eq_const {_ : MeasurableSpace α} [Measur
ableSpace β] [MeasurableSingletonClass β] {f : α -> β} (hf : Measurable f) (a : 
β) : Meas…
-/
lemma Measurable.const_eq {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : α → β} (hf : Measurable f) (a : β) : Measurable fun x => a = f x := by
  conv => enter [1, x]; rw [eq_comm]
  exact .eq_const hf a

section Set
variable [MeasurableSpace β] {g : β → Set α}

/-- This instance is useful when talking about Bernoulli sequences of random variables or binomial
random graphs. -/
/-
**Set.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.instMeasurableSpace : MeasurableSpace (Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is useful when talking about Bernoulli sequences of random variabl
es or binomial
random graphs.
-/
instance Set.instMeasurableSpace : MeasurableSpace (Set α) :=
  inferInstanceAs <| MeasurableSpace (α → Prop)
/-
**Set.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.instMeasurableSingletonClass [Countable α] : MeasurableSingletonClass 
(Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Set.instMeasurableSingletonClass [Countable α] : MeasurableSingletonClass (Set α) :=
  inferInstanceAs <| MeasurableSingletonClass (α → Prop)
/-
**measurable_setOfPred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1}, Measurable fun p => {a | p a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
@[simp, fun_prop] lemma measurable_setOfPred :
    Measurable fun p : α → Prop ↦ {a | p a} := measurable_id

@[deprecated (since := "2026-07-09")]
alias measurable_setOf := measurable_setOfPred
/-
**measurable_set_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_set_iff : Measurable g ↔ forall a, Measurable fun x => a in g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
-/
lemma measurable_set_iff : Measurable g ↔ ∀ a, Measurable fun x ↦ a ∈ g x := measurable_pi_iff

@[fun_prop]
/-
**measurable_set_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_set_mem (a : α) : Measurable fun s : Set α => a in s
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma measurable_set_mem (a : α) : Measurable fun s : Set α ↦ a ∈ s := measurable_pi_apply _
/-
**measurable_set_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_set_notMem (a : α) : Measurable fun s : Set α => a ∉ s
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.of_discrete`：∀ {α : Type u_1} {β : Type u_2} [inst : Measurab
leSpace α] [inst_1 : MeasurableSpace β] [DiscreteMeasurableSpace α]   {f : α → β
}, Measurabl…
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用引理 `measurable_set_mem`：measurable_set_mem (a : α) : Measurable fun s : Set 
α => a in s
-/
lemma measurable_set_notMem (a : α) : Measurable fun s : Set α ↦ a ∉ s :=
  (Measurable.of_discrete (f := Not)).comp <| measurable_set_mem a
/-
**measurableSet_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_mem (a : α) : MeasurableSet {s : Set α | a in s}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用引理 `measurable_set_mem`：measurable_set_mem (a : α) : Measurable fun s : Set 
α => a in s
-/
lemma measurableSet_mem (a : α) : MeasurableSet {s : Set α | a ∈ s} :=
  measurableSet_setOfPred.2 <| measurable_set_mem _
/-
**measurableSet_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_notMem (a : α) : MeasurableSet {s : Set α | a ∉ s}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用引理 `measurable_set_notMem`：measurable_set_notMem (a : α) : Measurable fun s 
: Set α => a ∉ s
-/
lemma measurableSet_notMem (a : α) : MeasurableSet {s : Set α | a ∉ s} :=
  measurableSet_setOfPred.2 <| measurable_set_notMem _
/-
**measurable_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_compl : Measurable ((·ᶜ) : Set α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `measurable_set_iff`：measurable_set_iff : Measurable g ↔ forall a, Measur
able fun x => a in g x
· 使用引理 `measurable_set_notMem`：measurable_set_notMem (a : α) : Measurable fun s 
: Set α => a ∉ s
-/
lemma measurable_compl : Measurable ((·ᶜ) : Set α → Set α) :=
  measurable_set_iff.2 fun _ ↦ measurable_set_notMem _

variable [Countable α]
/-
**MeasurableSet.setOfPred_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.setOfPred_finite : MeasurableSet {s : Set α | s.Finite}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `Set.Countable.ofPred_finite`：∀ {α : Type u} [Countable α], {s | s.Finite
}.Countable
-/
lemma MeasurableSet.setOfPred_finite : MeasurableSet {s : Set α | s.Finite} :=
  Countable.ofPred_finite.measurableSet

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_finite := MeasurableSet.setOfPred_finite
/-
**MeasurableSet.setOfPred_infinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.setOfPred_infinite : MeasurableSet {s : Set α | s.Infinite}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasurableSet.setOfPred_finite`：MeasurableSet.setOfPred_finite : Measura
bleSet {s : Set α | s.Finite}
-/
lemma MeasurableSet.setOfPred_infinite : MeasurableSet {s : Set α | s.Infinite} :=
  .setOfPred_finite |> .compl

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_infinite := MeasurableSet.setOfPred_infinite
/-
**MeasurableSet.sep_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.sep_finite {S : Set (Set α)} (hS : MeasurableSet S) : Measur
ableSet {s in S | s.Finite}
参数：Set α；hS : MeasurableSet S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `MeasurableSet.setOfPred_finite`：MeasurableSet.setOfPred_finite : Measura
bleSet {s : Set α | s.Finite}
-/
lemma MeasurableSet.sep_finite {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s ∈ S | s.Finite} :=
  hS.inter .setOfPred_finite
/-
**MeasurableSet.sep_infinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.sep_infinite {S : Set (Set α)} (hS : MeasurableSet S) : Meas
urableSet {s in S | s.Infinite}
参数：Set α；hS : MeasurableSet S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `MeasurableSet.setOfPred_infinite`：MeasurableSet.setOfPred_infinite : Mea
surableSet {s : Set α | s.Infinite}
-/
lemma MeasurableSet.sep_infinite {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s ∈ S | s.Infinite} :=
  hS.inter .setOfPred_infinite

@[fun_prop]
/-
**Measurable.subset** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace β] [Countable α] {
s t : β → Set α},   Measurable s → Measurable t → Measurable fun a => s a ⊆ t a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measurable.forall`：Measurable.forall [Countable ι] {p : ι -> α -> Prop} 
(hp : forall i, Measurable (p i)) : Measurable fun a => forall i, p i a
· 使用引理 `Measurable.imp`：Measurable.imp (hp : Measurable p) (hq : Measurable q) :
 Measurable fun a => p a -> q a
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `measurable_set_mem`：measurable_set_mem (a : α) : Measurable fun s : Set 
α => a in s
-/
protected lemma Measurable.subset {s t : β → Set α} (hs : Measurable s) (hs : Measurable t) :
    Measurable fun a ↦ s a ⊆ t a :=
  .forall fun i ↦ .imp (by fun_prop) (by fun_prop)

end Set

section Finset
variable [MeasurableSpace β] {g : β → Finset α}

/-- We give `Finset α` the measurable structure inherited from `Set α`.

This is the smallest sigma-algebra generated by `(a ∈ ·)` for all `a : α`.
See `measurable_finset_iff`. -/
/-
**Finset.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finset.instMeasurableSpace : MeasurableSpace (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We give `Finset α` the measurable structure inherited from `Set α`.

This is the smallest sigma-algebra generated by `(a ∈ ·)` for all `a : α`.
See `measurable_finset_iff`.
-/
instance Finset.instMeasurableSpace : MeasurableSpace (Finset α) :=
  .comap SetLike.coe inferInstance
/-
**measurable_finset_iff_measurable_set** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_finset_iff_measurable_set : Measurable g ↔ Measurable (fun x =>
 (g x : Set α))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `measurable_comap_iff`：measurable_comap_iff {mα : MeasurableSpace α} {mγ 
: MeasurableSpace γ} {f : α -> β} {g : β -> γ} : Measurable[mα, mγ.comap g] f ↔ 
Measurable…
-/
lemma measurable_finset_iff_measurable_set : Measurable g ↔ Measurable (fun x ↦ (g x : Set α)) :=
  measurable_comap_iff
/-
**measurable_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_finset_iff : Measurable g ↔ forall a, Measurable (a in g ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `measurable_finset_iff_measurable_set`：measurable_finset_iff_measurable_s
et : Measurable g ↔ Measurable (fun x => (g x : Set α))
· 使用引理 `measurable_set_iff`：measurable_set_iff : Measurable g ↔ forall a, Measur
able fun x => a in g x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma measurable_finset_iff : Measurable g ↔ ∀ a, Measurable (a ∈ g ·) := by
  rw [measurable_finset_iff_measurable_set, measurable_set_iff]; rfl
/-
**measurableSet_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_finset_iff (S : Set (Finset α)) : MeasurableSet S ↔ exists S
' : Set (Set α), MeasurableSet S' ∧ { s : Finset α | ↑s in S'} = S
参数：S : Set (Finset α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableSpace.measurableSet_comap`：measurableSet_comap {m : Measurable
Space β} : MeasurableSet[m.comap f] s ↔ exists s', MeasurableSet[m] s' ∧ f ⁻¹' s
' = s
-/
lemma measurableSet_finset_iff (S : Set (Finset α)) : MeasurableSet S ↔
    ∃ S' : Set (Set α), MeasurableSet S' ∧ { s : Finset α | ↑s ∈ S'} = S :=
  MeasurableSpace.measurableSet_comap

@[fun_prop]
/-
**measurable_finset_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_finset_mem (a : α) : Measurable fun s : Finset α => a in s
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `measurable_set_mem`：measurable_set_mem (a : α) : Measurable fun s : Set 
α => a in s
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
-/
lemma measurable_finset_mem (a : α) : Measurable fun s : Finset α ↦ a ∈ s :=
  (measurable_set_mem a).comp (comap_measurable _)
/-
**measurable_finset_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_finset_notMem (a : α) : Measurable fun s : Finset α => a ∉ s
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `measurable_set_notMem`：measurable_set_notMem (a : α) : Measurable fun s 
: Set α => a ∉ s
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
-/
lemma measurable_finset_notMem (a : α) : Measurable fun s : Finset α ↦ a ∉ s :=
  (measurable_set_notMem a).comp (comap_measurable _)
/-
**measurableSet_mem_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_mem_finset (a : α) : MeasurableSet {s : Finset α | a in s}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用引理 `measurable_finset_mem`：measurable_finset_mem (a : α) : Measurable fun s 
: Finset α => a in s
-/
lemma measurableSet_mem_finset (a : α) : MeasurableSet {s : Finset α | a ∈ s} :=
  measurableSet_setOfPred.2 <| measurable_finset_mem _
/-
**measurableSet_notMem_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_notMem_finset (a : α) : MeasurableSet {s : Finset α | a ∉ s}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用引理 `measurable_finset_notMem`：measurable_finset_notMem (a : α) : Measurable 
fun s : Finset α => a ∉ s
-/
lemma measurableSet_notMem_finset (a : α) : MeasurableSet {s : Finset α | a ∉ s} :=
  measurableSet_setOfPred.2 <| measurable_finset_notMem _

variable [Countable α]
/-
**Finset.instMeasurableSingletonClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finset.instMeasurableSingletonClass : MeasurableSingletonClass (Finset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `measurableSet_finset_iff`：measurableSet_finset_iff (S : Set (Finset α)) 
: MeasurableSet S ↔ exists S' : Set (Set α), MeasurableSet S' ∧ { s : Finset α |
 ↑s in S'} = S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance Finset.instMeasurableSingletonClass : MeasurableSingletonClass (Finset α) :=
  .mk fun S ↦ (measurableSet_finset_iff _).mpr ⟨{↑S}, by simp, by ext; simp⟩

end Finset

section curry

variable {ι : Type*}

section Function

variable {κ X : Type*} [MeasurableSpace X]

@[fun_prop]
/-
**measurable_curry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_curry : Measurable (@curry ι κ X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma measurable_curry : Measurable (@curry ι κ X) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

-- This cannot be tagged with `fun_prop` because `fun_prop` can see through `Function.uncurry`.
/-
**measurable_uncurry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_uncurry : Measurable (@uncurry ι κ X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma measurable_uncurry : Measurable (@uncurry ι κ X) := by fun_prop

@[fun_prop]
/-
**measurable_equivCurry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_equivCurry : Measurable (Equiv.curry ι κ X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `measurable_curry`：measurable_curry : Measurable (@curry ι κ X)
-/
lemma measurable_equivCurry : Measurable (Equiv.curry ι κ X) := measurable_curry

@[fun_prop]
/-
**measurable_equivCurry_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_equivCurry_symm : Measurable (Equiv.curry ι κ X).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `measurable_uncurry`：measurable_uncurry : Measurable (@uncurry ι κ X)
-/
lemma measurable_equivCurry_symm : Measurable (Equiv.curry ι κ X).symm := measurable_uncurry

end Function

section Sigma

variable {κ : ι → Type*} {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]

@[fun_prop]
/-
**measurable_sigmaCurry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_sigmaCurry : Measurable (Sigma.curry (γ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma measurable_sigmaCurry : Measurable (Sigma.curry (γ := X)) :=
    measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[fun_prop]
/-
**measurable_sigmaUncurry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_sigmaUncurry : Measurable (Sigma.uncurry (γ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma measurable_sigmaUncurry : Measurable (Sigma.uncurry (γ := X)) := by
  refine measurable_pi_lambda _ fun _ ↦ ?_
  simp only [Sigma.uncurry]
  fun_prop

@[fun_prop]
/-
**measurable_piCurry** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_piCurry : Measurable (Equiv.piCurry X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `measurable_sigmaCurry`：measurable_sigmaCurry : Measurable (Sigma.curry (
γ
-/
lemma measurable_piCurry : Measurable (Equiv.piCurry X) := measurable_sigmaCurry

@[fun_prop]
/-
**measurable_piCurry_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_piCurry_symm : Measurable (Equiv.piCurry X).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `measurable_sigmaUncurry`：measurable_sigmaUncurry : Measurable (Sigma.unc
urry (γ
-/
lemma measurable_piCurry_symm : Measurable (Equiv.piCurry X).symm := measurable_sigmaUncurry

end Sigma

end curry

variable (α) in
/-- Typeclass for a measurable space `α` for which the diagonal of `α × α` is measurable. -/
/-
**MeasurableEq** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [MeasurableSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a measurable space `α` for which the diagonal of `α × α` is measur
able.
-/
class MeasurableEq [MeasurableSpace α] where
  measurableSet_diagonal : MeasurableSet (diagonal α)

export MeasurableEq (measurableSet_diagonal)

attribute [measurability] measurableSet_diagonal
/-
**measurableSet_eq_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_eq_fun {m : MeasurableSpace α} [MeasurableSpace β] [Measurab
leEq β] {f g : α -> β} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {
x | f x = g x}
参数：hf : Measurable f；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasurableEq.measurableSet_diagonal`：∀ {α : Type u_1} {inst : Measurable
Space α} [self : MeasurableEq α], MeasurableSet (Set.diagonal α)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
-/
theorem measurableSet_eq_fun {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
    {f g : α → β} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} :=
  measurableSet_diagonal.preimage (hf.prodMk hg)

@[fun_prop]
/-
**Measurable.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.eq {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
 {f g : α -> β} (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f 
x = g x
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurableSet_setOfPred`：∀ {α : Type u_1} [inst : MeasurableSpace α] {p 
: α → Prop}, MeasurableSet {a | p a} ↔ Measurable p
· 使用定理 `measurableSet_eq_fun`：measurableSet_eq_fun {m : MeasurableSpace α} [Meas
urableSpace β] [MeasurableEq β] {f g : α -> β} (hf : Measurable f) (hg : Measura
ble g) : M…
-/
theorem Measurable.eq {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
    {f g : α → β} (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x = g x :=
  measurableSet_setOfPred.mp (measurableSet_eq_fun hf hg)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MeasurableSpace α] [MeasurableEq α] : MeasurableSingletonClass α := by
  constructor
  simp_rw [← ofPred_eq_eq_singleton, measurableSet_setOfPred]
  measurability
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] : MeasurableEq α := by
  constructor
  simp_rw [← Set.range_diag, Set.range_eq_iUnion]
  measurability
