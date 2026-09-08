/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Projective measure families and projective limits

A family of measures indexed by finite sets of `ι` is projective if, for finite sets `J ⊆ I`,
the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`.
A measure `μ` is the projective limit of such a family of measures if for all `I : Finset ι`,
the projection from `∀ i, α i` to `∀ i : I, α i` maps `μ` to `P I`.

## Main definitions

* `MeasureTheory.IsProjectiveMeasureFamily`: `P : ∀ J : Finset ι, Measure (∀ j : J, α j)` is
  projective if the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`
  for all `J ⊆ I`.
* `MeasureTheory.IsProjectiveLimit`: `μ` is the projective limit of the measure family `P` if for
  all `I : Finset ι`, the map of `μ` by the projection to `I` is `P I`.

## Main statements

* `MeasureTheory.IsProjectiveLimit.unique`: the projective limit of a family of finite measures
  is unique.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

/-- A family of measures indexed by finite sets of `ι` is projective if, for finite sets `J ⊆ I`,
the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`. -/
/-
**MeasureTheory.IsProjectiveMeasureFamily** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry`。
形式化陈述：IsProjectiveMeasureFamily (P : forall J : Finset ι, Measure (forall j : J,
 α j)) : Prop
参数：P : forall J : Finset ι, Measure (forall j : J, α j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of measures indexed by finite sets of `ι` is projective if, for finite 
sets `J ⊆ I`,
the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`.
-/
def IsProjectiveMeasureFamily (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ (I J : Finset ι) (hJI : J ⊆ I),
    P J = (P I).map (Finset.restrict₂ hJI)

namespace IsProjectiveMeasureFamily

variable {I J : Finset ι}

/-
**MeasureTheory.IsProjectiveMeasureFamily.eq_zero_of_isEmpty** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.IsProjectiveMeasureFamily`。
形式化陈述：eq_zero_of_isEmpty [h : IsEmpty (Π i, α i)] (hP : IsProjectiveMeasureFamil
y P) (I : Finset ι) : P I = 0
参数：Π i, α i；hP : IsProjectiveMeasureFamily P；I : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isEmpty_pi`：isEmpty_pi {π : α -> Sort*} : IsEmpty (forall a, π a) ↔ exis
ts a, IsEmpty (π a)
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.Measure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEmpty α]
 {_m : MeasurableSpace α} (μ : Measure α) : μ = 0
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_zero_of_isEmpty [h : IsEmpty (Π i, α i)]
    (hP : IsProjectiveMeasureFamily P) (I : Finset ι) :
    P I = 0 := by
  classical
  obtain ⟨i, hi⟩ := isEmpty_pi.mp h
  rw [hP (insert i I) I (I.subset_insert i)]
  have : IsEmpty (Π j : ↑(insert i I), α j) := by simp [hi]
  rw [(P (insert i I)).eq_zero_of_isEmpty]
  simp

/-- Auxiliary lemma for `measure_univ_eq`. -/
/-
**MeasureTheory.IsProjectiveMeasureFamily.measure_univ_eq_of_subset** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.IsProjectiveMeasureFamily`。
形式化陈述：measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P) (hJI : J subs
eteq I) : P I univ = P J univ
参数：hP : IsProjectiveMeasureFamily P；hJI : J subseteq I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ

--- 原说明 ---
Auxiliary lemma for `measure_univ_eq`.
-/
lemma measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P) (hJI : J ⊆ I) :
    P I univ = P J univ := by
  have : (univ : Set (∀ i : I, α i)) =
      Finset.restrict₂ hJI ⁻¹' (univ : Set (∀ i : J, α i)) := by
    rw [preimage_univ]
  rw [this, ← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
/-
**MeasureTheory.IsProjectiveMeasureFamily.measure_univ_eq** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.IsProjectiveMeasureFamily`。
形式化陈述：measure_univ_eq (hP : IsProjectiveMeasureFamily P) (I J : Finset ι) : P I 
univ = P J univ
参数：hP : IsProjectiveMeasureFamily P；I J : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.IsProjectiveMeasureFamily.measure_univ_eq_of_subset`：measu
re_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P) (hJI : J subseteq I) : P
 I univ = P J univ
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
-/
lemma measure_univ_eq (hP : IsProjectiveMeasureFamily P) (I J : Finset ι) :
    P I univ = P J univ := by
  classical
  rw [← hP.measure_univ_eq_of_subset I.subset_union_left,
    ← hP.measure_univ_eq_of_subset (I.subset_union_right (s₂ := J))]
/-
**MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder_of_subset** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.IsProjectiveMeasureFamily`。
形式化陈述：congr_cylinder_of_subset (hP : IsProjectiveMeasureFamily P) {S : Set (fora
ll i : I, α i)} {T : Set (forall i : J, α i)} (hT : MeasurableSet T) (h_eq : cyl
inder I S = cylinder J T) (hJI : J subseteq I) : P I S = P J T
参数：hP : IsProjectiveMeasureFamily P；forall i : I, α i；forall i : J, α i；hT : Mea
surableSet T；h_eq : cylinder I S = cylinder J T；hJI : J subseteq I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `MeasureTheory.IsProjectiveMeasureFamily.eq_zero_of_isEmpty`：eq_zero_of_i
sEmpty [h : IsEmpty (Π i, α i)] (hP : IsProjectiveMeasureFamily P) (I : Finset ι
) : P I = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eq_of_cylinder_eq_of_subset`：eq_of_cylinder_eq_of_subset [
h_nonempty : Nonempty (forall i, α i)] {I J : Finset ι} {S : Set (forall i : I, 
α i)} {T : Set (forall i : J, α…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma congr_cylinder_of_subset (hP : IsProjectiveMeasureFamily P)
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) (hJI : J ⊆ I) :
    P I S = P J T := by
  cases isEmpty_or_nonempty (∀ i, α i) with
  | inl h =>
    suffices ∀ I, P I univ = 0 by
      simp only [Measure.measure_univ_eq_zero] at this
      simp [this]
    simpa using eq_zero_of_isEmpty hP
  | inr h =>
    have : S = Finset.restrict₂ hJI ⁻¹' T :=
      eq_of_cylinder_eq_of_subset h_eq hJI
    rw [hP I J hJI, Measure.map_apply _ hT, this]
    exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
/-
**MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.IsProjectiveMeasureFamily`。
形式化陈述：congr_cylinder (hP : IsProjectiveMeasureFamily P) {S : Set (forall i : I, 
α i)} {T : Set (forall i : J, α i)} (hS : MeasurableSet S) (hT : MeasurableSet T
) (h_eq : cylinder I S = cylinder J T) : P I S = P J T
参数：hP : IsProjectiveMeasureFamily P；forall i : I, α i；forall i : J, α i；hS : Mea
surableSet S；hT : MeasurableSet T；h_eq : cylinder I S = cylinder J T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.inter_cylinder`：inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Se
t (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i)) [DecidableEq ι] : cylind
er s₁ S₁ inter cyl…
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用引理 `MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder_of_subset`：congr_
cylinder_of_subset (hP : IsProjectiveMeasureFamily P) {S : Set (forall i : I, α 
i)} {T : Set (forall i : J, α i)} (hT : MeasurableSet …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma congr_cylinder (hP : IsProjectiveMeasureFamily P)
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) :
    P I S = P J T := by
  classical
  let U := Finset.restrict₂ Finset.subset_union_left ⁻¹' S ∩
      Finset.restrict₂ Finset.subset_union_right ⁻¹' T
  suffices P (I ∪ J) U = P I S ∧ P (I ∪ J) U = P J T from this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_of_subset hS h_eq_union.symm Finset.subset_union_left
  · have h_eq_union : cylinder J T = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_of_subset hT h_eq_union.symm Finset.subset_union_right

end IsProjectiveMeasureFamily

/-- A measure `μ` is the projective limit of a family of measures indexed by finite sets of `ι` if
for all `I : Finset ι`, the projection from `∀ i, α i` to `∀ i : I, α i` maps `μ` to `P I`. -/
/-
**MeasureTheory.IsProjectiveLimit** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：IsProjectiveLimit (μ : Measure (forall i, α i)) (P : forall J : Finset ι, 
Measure (forall j : J, α j)) : Prop
参数：μ : Measure (forall i, α i)；P : forall J : Finset ι, Measure (forall j : J, α
 j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is the projective limit of a family of measures indexed by finite 
sets of `ι` if
for all `I : Finset ι`, the projection from `∀ i, α i` to `∀ i : I, α i` maps `μ
` to `P I`.
-/
def IsProjectiveLimit (μ : Measure (∀ i, α i))
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ I : Finset ι, (μ.map I.restrict) = P I

namespace IsProjectiveLimit

variable {μ ν : Measure (∀ i, α i)}

/-
**MeasureTheory.IsProjectiveLimit.measure_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.IsProjectiveLimit`。
形式化陈述：measure_cylinder (h : IsProjectiveLimit μ P) (I : Finset ι) {s : Set (fora
ll i : I, α i)} (hs : MeasurableSet s) : μ (cylinder I s) = P I s
参数：h : IsProjectiveLimit μ P；I : Finset ι；forall i : I, α i；hs : MeasurableSet s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cylinder.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} (s : Fi
nset ι) (S : Set ((i : ↥s) → α ↑i)),   MeasureTheory.cylinder s S = s.restrict ⁻
¹' S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma measure_cylinder (h : IsProjectiveLimit μ P)
    (I : Finset ι) {s : Set (∀ i : I, α i)} (hs : MeasurableSet s) :
    μ (cylinder I s) = P I s := by
  rw [cylinder, ← Measure.map_apply _ hs, h I]
  exact measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
/-
**MeasureTheory.IsProjectiveLimit.measure_univ_eq** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.IsProjectiveLimit`。
形式化陈述：measure_univ_eq (hμ : IsProjectiveLimit μ P) (I : Finset ι) : μ univ = P I
 univ
参数：hμ : IsProjectiveLimit μ P；I : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.cylinder_univ`：cylinder_univ (s : Finset ι) : cylinder s (
univ : Set (forall i : s, α i)) = univ
· 使用引理 `MeasureTheory.IsProjectiveLimit.measure_cylinder`：measure_cylinder (h : 
IsProjectiveLimit μ P) (I : Finset ι) {s : Set (forall i : I, α i)} (hs : Measur
ableSet s) : μ (cylinder I s) = P I s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma measure_univ_eq (hμ : IsProjectiveLimit μ P) (I : Finset ι) :
    μ univ = P I univ := by
  rw [← cylinder_univ I, hμ.measure_cylinder _ MeasurableSet.univ]
/-
**MeasureTheory.IsProjectiveLimit.isFiniteMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.IsProjectiveLimit`。
形式化陈述：isFiniteMeasure [forall i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit 
μ P) : IsFiniteMeasure μ
参数：P i；hμ : IsProjectiveLimit μ P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.IsProjectiveLimit.measure_univ_eq`：measure_univ_eq (hμ : I
sProjectiveLimit μ P) (I : Finset ι) : μ univ = P I univ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
lemma isFiniteMeasure [∀ i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) :
    IsFiniteMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_lt_top _ _
/-
**MeasureTheory.IsProjectiveLimit.isProbabilityMeasure** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.IsProjectiveLimit`。
形式化陈述：isProbabilityMeasure [forall i, IsProbabilityMeasure (P i)] (hμ : IsProjec
tiveLimit μ P) : IsProbabilityMeasure μ
参数：P i；hμ : IsProjectiveLimit μ P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.IsProjectiveLimit.measure_univ_eq`：measure_univ_eq (hμ : I
sProjectiveLimit μ P) (I : Finset ι) : μ univ = P I univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
lemma isProbabilityMeasure [∀ i, IsProbabilityMeasure (P i)] (hμ : IsProjectiveLimit μ P) :
    IsProbabilityMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_univ
/-
**MeasureTheory.IsProjectiveLimit.measure_univ_unique** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.IsProjectiveLimit`。
形式化陈述：measure_univ_unique (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν
 P) : μ univ = ν univ
参数：hμ : IsProjectiveLimit μ P；hν : IsProjectiveLimit ν P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.IsProjectiveLimit.measure_univ_eq`：measure_univ_eq (hμ : I
sProjectiveLimit μ P) (I : Finset ι) : μ univ = P I univ
-/
lemma measure_univ_unique (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ univ = ν univ := by
  rw [hμ.measure_univ_eq (∅ : Finset ι), hν.measure_univ_eq (∅ : Finset ι)]

/-- The projective limit of a family of finite measures is unique. -/
/-
**MeasureTheory.IsProjectiveLimit.unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.IsProjectiveLimit`。
形式化陈述：unique [forall i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) (hν 
: IsProjectiveLimit ν P) : μ = ν
参数：P i；hμ : IsProjectiveLimit μ P；hν : IsProjectiveLimit ν P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.IsProjectiveLimit.isFiniteMeasure`：isFiniteMeasure [forall
 i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) : IsFiniteMeasure μ
· 使用定理 `MeasureTheory.ext_of_generate_finite`：ext_of_generate_finite (C : Set (S
et α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C) [IsFiniteMeasure μ] (hμν :
 forall s in C, μ s = ν s)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.generateFrom_measurableCylinders`：generateFrom_measurableC
ylinders : MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpac
e.pi
· 使用定理 `MeasureTheory.isPiSystem_measurableCylinders`：isPiSystem_measurableCylin
ders : IsPiSystem (measurableCylinders α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.IsProjectiveLimit.measure_cylinder`：measure_cylinder (h : 
IsProjectiveLimit μ P) (I : Finset ι) {s : Set (forall i : I, α i)} (hs : Measur
ableSet s) : μ (cylinder I s) = P I s
· 使用引理 `MeasureTheory.IsProjectiveLimit.measure_univ_unique`：measure_univ_unique
 (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) : μ univ = ν univ

--- 原说明 ---
The projective limit of a family of finite measures is unique.
-/
theorem unique [∀ i, IsFiniteMeasure (P i)]
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ = ν := by
  have : IsFiniteMeasure μ := hμ.isFiniteMeasure
  refine ext_of_generate_finite (measurableCylinders α) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs ↦ ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [hμ.measure_cylinder _ hS, hν.measure_cylinder _ hS]

end IsProjectiveLimit

end MeasureTheory

