/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.SetAlgebra

/-!
# Additive content built from a projective family of measures

Let `P` be a projective family of measures on a family of measurable spaces indexed by `ι`.
That is, for each finite set `I` of indices, `P I` is a measure on `Π j : I, α j`, and for `J ⊆ I`,
the projection from `Π i : I, α i` to `Π i : J, α i` maps `P I` to `P J`.

We build an additive content `projectiveFamilyContent` on the measurable cylinders, by setting
`projectiveFamilyContent s = P I S` for `s = cylinder I S`, where `I` is a finite set of indices
and `S` is a measurable set in `Π i : I, α i`.

This content will be used to define the projective limit of the family of measures `P`.
For a countable index set and a projective family given by a sequence of kernels,
the projective limit is given by the Ionescu-Tulcea theorem.
For an arbitrary index set but under topological conditions on the spaces, this is the result of
the Kolmogorov extension theorem.
(both results are not yet in Mathlib)

## Main definitions

* `projectiveFamilyContent`: additive content on the measurable cylinders, defined from a projective
  family of measures.

-/

@[expose] public section


open Finset

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)}
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)} {s t : Set (Π i, α i)} {I : Finset ι}
  {S : Set (Π i : I, α i)}

section MeasurableCylinders

/-
**MeasureTheory.isSetAlgebra_measurableCylinders** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：isSetAlgebra_measurableCylinders : IsSetAlgebra (measurableCylinders α) wh
ere empty_mem
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.empty_mem_measurableCylinders`：empty_mem_measurableCylinde
rs (α : ι -> Type*) [forall i, MeasurableSpace (α i)] : ∅ in measurableCylinders
 α
· 使用定理 `MeasureTheory.compl_mem_measurableCylinders`：compl_mem_measurableCylinde
rs (hs : s in measurableCylinders α) : sᶜ in measurableCylinders α
· 使用定理 `MeasureTheory.union_mem_measurableCylinders`：union_mem_measurableCylinde
rs (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) : s union
 t in measurableCylinders α
-/
lemma isSetAlgebra_measurableCylinders : IsSetAlgebra (measurableCylinders α) where
  empty_mem := empty_mem_measurableCylinders α
  compl_mem _ := compl_mem_measurableCylinders
  union_mem _ _ := union_mem_measurableCylinders
/-
**MeasureTheory.isSetRing_measurableCylinders** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：isSetRing_measurableCylinders : IsSetRing (measurableCylinders α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsSetAlgebra.isSetRing`：isSetRing (h𝒜 : IsSetAlgebra 𝒜) : 
IsSetRing 𝒜 where empty_mem
· 使用引理 `MeasureTheory.isSetAlgebra_measurableCylinders`：isSetAlgebra_measurableC
ylinders : IsSetAlgebra (measurableCylinders α) where empty_mem
-/
lemma isSetRing_measurableCylinders : IsSetRing (measurableCylinders α) :=
  isSetAlgebra_measurableCylinders.isSetRing
/-
**MeasureTheory.isSetSemiring_measurableCylinders** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：isSetSemiring_measurableCylinders : MeasureTheory.IsSetSemiring (measurabl
eCylinders α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.IsSetRing.isSetSemiring`：isSetSemiring (hC : IsSetRing C) 
: IsSetSemiring C where empty_mem
· 使用引理 `MeasureTheory.isSetRing_measurableCylinders`：isSetRing_measurableCylinde
rs : IsSetRing (measurableCylinders α)
-/
lemma isSetSemiring_measurableCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α) :=
  isSetRing_measurableCylinders.isSetSemiring

end MeasurableCylinders

section ProjectiveFamilyFun

open scoped Classical in
/-- For `P` a family of measures, with `P J` a measure on `Π j : J, α j`, we define a function
`projectiveFamilyFun P s` by setting it to `P I S` if `s = cylinder I S` for a measurable `S` and
to 0 if `s` is not a measurable cylinder. -/
/-
**MeasureTheory.projectiveFamilyFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：projectiveFamilyFun (P : forall J : Finset ι, Measure (Π j : J, α j)) (s :
 Set (Π i, α i)) : Real>=0∞
参数：P : forall J : Finset ι, Measure (Π j : J, α j)；s : Set (Π i, α i)。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `P` a family of measures, with `P J` a measure on `Π j : J, α j`, we define 
a function
`projectiveFamilyFun P s` by setting it to `P I S` if `s = cylinder I S` for a m
easurable `S` and
to 0 if `s` is not a measurable cylinder.
-/
noncomputable def projectiveFamilyFun (P : ∀ J : Finset ι, Measure (Π j : J, α j))
    (s : Set (Π i, α i)) : ℝ≥0∞ :=
  if hs : s ∈ measurableCylinders α
    then P (measurableCylinders.finset hs) (measurableCylinders.set hs) else 0
/-
**MeasureTheory.projectiveFamilyFun_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：projectiveFamilyFun_congr (hP : IsProjectiveMeasureFamily P) (hs : s in me
asurableCylinders α) (hs_eq : s = cylinder I S) (hS : MeasurableSet S) : project
iveFamilyFun P s = P I S
参数：hP : IsProjectiveMeasureFamily P；hs : s in measurableCylinders α；hs_eq : s = 
cylinder I S；hS : MeasurableSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.projectiveFamilyFun.eq_1`：∀ {ι : Type u_1} {α : ι → Type u
_2} {mα : (i : ι) → MeasurableSpace (α i)}   (P : (J : Finset ι) → MeasureTheory
.Measure ((j : ↥J) → α ↑j)) …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `MeasureTheory.IsProjectiveMeasureFamily.congr_cylinder`：congr_cylinder (
hP : IsProjectiveMeasureFamily P) {S : Set (forall i : I, α i)} {T : Set (forall
 i : J, α i)} (hS : MeasurableSet S) (hT : M…
· 使用定理 `MeasureTheory.measurableCylinders.measurableSet`：∀ {ι : Type u_1} {α : ι
 → Type u_2} [inst : (i : ι) → MeasurableSpace (α i)] {t : Set ((i : ι) → α i)} 
  (ht : t ∈ MeasureTheory.measurableC…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measurableCylinders.eq_cylinder`：∀ {ι : Type u_1} {α : ι →
 Type u_2} [inst : (i : ι) → MeasurableSpace (α i)] {t : Set ((i : ι) → α i)}   
(ht : t ∈ MeasureTheory.measurableC…
-/
lemma projectiveFamilyFun_congr (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    projectiveFamilyFun P s = P I S := by
  rw [projectiveFamilyFun, dif_pos hs]
  exact hP.congr_cylinder (measurableCylinders.measurableSet hs) hS
    ((measurableCylinders.eq_cylinder hs).symm.trans hs_eq)
/-
**MeasureTheory.projectiveFamilyFun_empty** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：projectiveFamilyFun_empty (hP : IsProjectiveMeasureFamily P) : projectiveF
amilyFun P ∅ = 0
参数：hP : IsProjectiveMeasureFamily P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.projectiveFamilyFun_congr`：projectiveFamilyFun_congr (hP :
 IsProjectiveMeasureFamily P) (hs : s in measurableCylinders α) (hs_eq : s = cyl
inder I S) (hS : MeasurableSe…
· 使用定理 `MeasureTheory.empty_mem_measurableCylinders`：empty_mem_measurableCylinde
rs (α : ι -> Type*) [forall i, MeasurableSpace (α i)] : ∅ in measurableCylinders
 α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.cylinder_empty`：cylinder_empty (s : Finset ι) : cylinder s
 (∅ : Set (forall i : s, α i)) = ∅
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma projectiveFamilyFun_empty (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyFun P ∅ = 0 := by
  rw [projectiveFamilyFun_congr hP (empty_mem_measurableCylinders α) (cylinder_empty ∅).symm
    MeasurableSet.empty, measure_empty]
/-
**MeasureTheory.projectiveFamilyFun_union** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：projectiveFamilyFun_union (hP : IsProjectiveMeasureFamily P) (hs : s in me
asurableCylinders α) (ht : t in measurableCylinders α) (hst : Disjoint s t) : pr
ojectiveFamilyFun P (s union t) = projectiveFamilyFun P s + projectiveFamilyFun 
P t
参数：hP : IsProjectiveMeasureFamily P；hs : s in measurableCylinders α；ht : t in me
asurableCylinders α；hst : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cylinder_eq_cylinder_union`：cylinder_eq_cylinder_union [De
cidableEq ι] (I : Finset ι) (S : Set (forall i : I, α i)) (J : Finset ι) : cylin
der I S = cylinder (I union J)…
· 使用定理 `MeasureTheory.union_cylinder`：union_cylinder (s₁ s₂ : Finset ι) (S₁ : Se
t (forall i : s₁, α i)) (S₂ : Set (forall i : s₂, α i)) [DecidableEq ι] : cylind
er s₁ S₁ union cyl…
· 使用引理 `MeasureTheory.projectiveFamilyFun_congr`：projectiveFamilyFun_congr (hP :
 IsProjectiveMeasureFamily P) (hs : s in measurableCylinders α) (hs_eq : s = cyl
inder I S) (hS : MeasurableSe…
· 使用定理 `MeasureTheory.union_mem_measurableCylinders`：union_mem_measurableCylinde
rs (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) : s union
 t in measurableCylinders α
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.IsProjectiveMeasureFamily.eq_zero_of_isEmpty`：eq_zero_of_i
sEmpty [h : IsEmpty (Π i, α i)] (hP : IsProjectiveMeasureFamily P) (I : Finset ι
) : P I = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `MeasureTheory.disjoint_cylinder_iff`：disjoint_cylinder_iff [Nonempty (fo
rall i, α i)] {s t : Finset ι} {S : Set (forall i : s, α i)} {T : Set (forall i 
: t, α i)} [DecidableEq ι…
-/
lemma projectiveFamilyFun_union (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) (hst : Disjoint s t) :
    projectiveFamilyFun P (s ∪ t) = projectiveFamilyFun P s + projectiveFamilyFun P t := by
  obtain ⟨I, S, hS, hs_eq⟩ := (mem_measurableCylinders _).1 hs
  obtain ⟨J, T, hT, ht_eq⟩ := (mem_measurableCylinders _).1 ht
  classical
  let S' := restrict₂ (subset_union_left (s₂ := J)) ⁻¹' S
  let T' := restrict₂ (subset_union_right (s₁ := I)) ⁻¹' T
  have hS' : MeasurableSet S' := measurable_restrict₂ _ hS
  have hT' : MeasurableSet T' := measurable_restrict₂ _ hT
  have h_eq1 : s = cylinder (I ∪ J) S' := by rw [hs_eq]; exact cylinder_eq_cylinder_union I S J
  have h_eq2 : t = cylinder (I ∪ J) T' := by rw [ht_eq]; exact cylinder_eq_cylinder_union J T I
  have h_eq3 : s ∪ t = cylinder (I ∪ J) (S' ∪ T') := by
    rw [hs_eq, ht_eq]; exact union_cylinder _ _ _ _
  rw [projectiveFamilyFun_congr hP hs h_eq1 hS', projectiveFamilyFun_congr hP ht h_eq2 hT',
    projectiveFamilyFun_congr hP (union_mem_measurableCylinders hs ht) h_eq3 (hS'.union hT')]
  cases isEmpty_or_nonempty (Π i, α i) with
  | inl h => simp [hP.eq_zero_of_isEmpty]
  | inr h =>
    rw [measure_union _ hT']
    rwa [hs_eq, ht_eq, disjoint_cylinder_iff] at hst

end ProjectiveFamilyFun

section ProjectiveFamilyContent

/-- For `P` a projective family of measures, we define an additive content on the measurable
cylinders, by setting `projectiveFamilyContent s = P I S` for `s = cylinder I S`, where `I` is
a finite set of indices and `S` is a measurable set in `Π i : I, α i`. -/
/-
**MeasureTheory.projectiveFamilyContent** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
`。
形式化陈述：projectiveFamilyContent (hP : IsProjectiveMeasureFamily P) : AddContent Re
al>=0∞ (measurableCylinders α)
参数：hP : IsProjectiveMeasureFamily P。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.isSetRing_measurableCylinders`：isSetRing_measurableCylinde
rs : IsSetRing (measurableCylinders α)
· 使用引理 `MeasureTheory.projectiveFamilyFun_empty`：projectiveFamilyFun_empty (hP :
 IsProjectiveMeasureFamily P) : projectiveFamilyFun P ∅ = 0
· 使用引理 `MeasureTheory.projectiveFamilyFun_union`：projectiveFamilyFun_union (hP :
 IsProjectiveMeasureFamily P) (hs : s in measurableCylinders α) (ht : t in measu
rableCylinders α) (hst : Disj…

--- 原说明 ---
For `P` a projective family of measures, we define an additive content on the me
asurable
cylinders, by setting `projectiveFamilyContent s = P I S` for `s = cylinder I S`
, where `I` is
a finite set of indices and `S` is a measurable set in `Π i : I, α i`.
-/
noncomputable def projectiveFamilyContent (hP : IsProjectiveMeasureFamily P) :
    AddContent ℝ≥0∞ (measurableCylinders α) :=
  isSetRing_measurableCylinders.addContent_of_union (projectiveFamilyFun P)
    (projectiveFamilyFun_empty hP) (projectiveFamilyFun_union hP)
/-
**MeasureTheory.projectiveFamilyContent_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：projectiveFamilyContent_eq (hP : IsProjectiveMeasureFamily P) : projective
FamilyContent hP s = projectiveFamilyFun P s
参数：hP : IsProjectiveMeasureFamily P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma projectiveFamilyContent_eq (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyContent hP s = projectiveFamilyFun P s := rfl
/-
**MeasureTheory.projectiveFamilyContent_congr** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：projectiveFamilyContent_congr (hP : IsProjectiveMeasureFamily P) (s : Set 
(Π i, α i)) (hs_eq : s = cylinder I S) (hS : MeasurableSet S) : projectiveFamily
Content hP s = P I S
参数：hP : IsProjectiveMeasureFamily P；s : Set (Π i, α i)；hs_eq : s = cylinder I S；
hS : MeasurableSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.projectiveFamilyContent_eq`：projectiveFamilyContent_eq (hP
 : IsProjectiveMeasureFamily P) : projectiveFamilyContent hP s = projectiveFamil
yFun P s
· 使用引理 `MeasureTheory.projectiveFamilyFun_congr`：projectiveFamilyFun_congr (hP :
 IsProjectiveMeasureFamily P) (hs : s in measurableCylinders α) (hs_eq : s = cyl
inder I S) (hS : MeasurableSe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.mem_measurableCylinders`：mem_measurableCylinders (t : Set 
(forall i, α i)) : t in measurableCylinders α ↔ exists s S, MeasurableSet S ∧ t 
= cylinder s S
-/
lemma projectiveFamilyContent_congr (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i))
    (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    projectiveFamilyContent hP s = P I S := by
  rw [projectiveFamilyContent_eq,
    projectiveFamilyFun_congr hP ((mem_measurableCylinders s).mpr ⟨I, S, hS, hs_eq⟩) hs_eq hS]
/-
**MeasureTheory.projectiveFamilyContent_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：projectiveFamilyContent_cylinder (hP : IsProjectiveMeasureFamily P) (hS : 
MeasurableSet S) : projectiveFamilyContent hP (cylinder I S) = P I S
参数：hP : IsProjectiveMeasureFamily P；hS : MeasurableSet S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.projectiveFamilyContent_congr`：projectiveFamilyContent_con
gr (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i)) (hs_eq : s = cylinder
 I S) (hS : MeasurableSet S) : pr…
-/
lemma projectiveFamilyContent_cylinder (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S) :
    projectiveFamilyContent hP (cylinder I S) = P I S := projectiveFamilyContent_congr _ _ rfl hS
/-
**MeasureTheory.projectiveFamilyContent_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：projectiveFamilyContent_mono (hP : IsProjectiveMeasureFamily P) (hs : s in
 measurableCylinders α) (ht : t in measurableCylinders α) (hst : s subseteq t) :
 projectiveFamilyContent hP s <= projectiveFamilyContent hP t
参数：hP : IsProjectiveMeasureFamily P；hs : s in measurableCylinders α；ht : t in me
asurableCylinders α；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.addContent_mono`：addContent_mono (hC : IsSetSemiring C) (h
s : s in C) (ht : t in C) (hst : s subseteq t) : m s <= m t
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `MeasureTheory.isSetSemiring_measurableCylinders`：isSetSemiring_measurabl
eCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α)
-/
lemma projectiveFamilyContent_mono (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) (hst : s ⊆ t) :
    projectiveFamilyContent hP s ≤ projectiveFamilyContent hP t :=
  addContent_mono isSetSemiring_measurableCylinders hs ht hst
/-
**MeasureTheory.projectiveFamilyContent_iUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：projectiveFamilyContent_iUnion_le (hP : IsProjectiveMeasureFamily P) {s : 
Nat -> Set (Π i : ι, α i)} (hs : forall n, s n in measurableCylinders α) (n : Na
t) : projectiveFamilyContent hP (⋃ i <= n, s i) <= ∑ i in range (n + 1), project
iveFamilyContent hP (s i)
参数：hP : IsProjectiveMeasureFamily P；Π i : ι, α i；hs : forall n, s n in measurabl
eCylinders α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.addContent_biUnion_le`：addContent_biUnion_le {ι : Type*} (
hC : IsSetRing C) {s : ι -> Set α} {S : Finset ι} (hs : forall n in S, s n in C)
 : m (⋃ i in S, s i) <= ∑…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `MeasureTheory.isSetRing_measurableCylinders`：isSetRing_measurableCylinde
rs : IsSetRing (measurableCylinders α)
-/
lemma projectiveFamilyContent_iUnion_le (hP : IsProjectiveMeasureFamily P)
    {s : ℕ → Set (Π i : ι, α i)} (hs : ∀ n, s n ∈ measurableCylinders α) (n : ℕ) :
    projectiveFamilyContent hP (⋃ i ≤ n, s i)
      ≤ ∑ i ∈ range (n + 1), projectiveFamilyContent hP (s i) :=
  calc projectiveFamilyContent hP (⋃ i ≤ n, s i)
  _ = projectiveFamilyContent hP (⋃ i ∈ range (n + 1), s i) := by
    simp only [mem_range_succ_iff]
  _ ≤ ∑ i ∈ range (n + 1), projectiveFamilyContent hP (s i) :=
    addContent_biUnion_le isSetRing_measurableCylinders (fun i _ ↦ hs i)
/-
**MeasureTheory.projectiveFamilyContent_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：projectiveFamilyContent_ne_top [forall J, IsFiniteMeasure (P J)] (hP : IsP
rojectiveMeasureFamily P) : projectiveFamilyContent hP s != ∞
参数：P J；hP : IsProjectiveMeasureFamily P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.projectiveFamilyContent_eq`：projectiveFamilyContent_eq (hP
 : IsProjectiveMeasureFamily P) : projectiveFamilyContent hP s = projectiveFamil
yFun P s
· 使用定理 `MeasureTheory.projectiveFamilyFun.eq_1`：∀ {ι : Type u_1} {α : ι → Type u
_2} {mα : (i : ι) → MeasurableSpace (α i)}   (P : (J : Finset ι) → MeasureTheory
.Measure ((j : ↥J) → α ↑j)) …
· 使用定理 `dite_ne_top`：dite_ne_top {a : p -> α} {b : ¬p -> α} (ha : forall h, a h 
!= ⊤) (hb : forall h, b h != ⊤) : (if h : p then a h else b h) != ⊤
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
-/
lemma projectiveFamilyContent_ne_top [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyContent hP s ≠ ∞ := by
  rw [projectiveFamilyContent_eq hP, projectiveFamilyFun]
  finiteness
/-
**MeasureTheory.projectiveFamilyContent_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：projectiveFamilyContent_sdiff (hP : IsProjectiveMeasureFamily P) (hs : s i
n measurableCylinders α) (ht : t in measurableCylinders α) : projectiveFamilyCon
tent hP s - projectiveFamilyContent hP t <= projectiveFamilyContent hP (s \ t)
参数：hP : IsProjectiveMeasureFamily P；hs : s in measurableCylinders α；ht : t in me
asurableCylinders α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.le_addContent_sdiff`：le_addContent_sdiff (m : AddContent R
eal>=0∞ C) (hC : IsSetRing C) (hs : s in C) (ht : t in C) : m s - m t <= m (s \ 
t)
· 使用引理 `MeasureTheory.isSetRing_measurableCylinders`：isSetRing_measurableCylinde
rs : IsSetRing (measurableCylinders α)
-/
lemma projectiveFamilyContent_sdiff (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) :
    projectiveFamilyContent hP s - projectiveFamilyContent hP t
      ≤ projectiveFamilyContent hP (s \ t) :=
  le_addContent_sdiff (projectiveFamilyContent hP) isSetRing_measurableCylinders hs ht

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff := projectiveFamilyContent_sdiff
/-
**MeasureTheory.projectiveFamilyContent_sdiff_of_subset** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：projectiveFamilyContent_sdiff_of_subset [forall J, IsFiniteMeasure (P J)] 
(hP : IsProjectiveMeasureFamily P) (hs : s in measurableCylinders α) (ht : t in 
measurableCylinders α) (hts : t subseteq s) : projectiveFamilyContent hP (s \ t)
 = projectiveFamilyContent hP s - projectiveFamilyContent hP t
参数：P J；hP : IsProjectiveMeasureFamily P；hs : s in measurableCylinders α；ht : t i
n measurableCylinders α；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.addContent_sdiff_of_ne_top`：addContent_sdiff_of_ne_top (m 
: AddContent Real>=0∞ C) (hC : IsSetRing C) (hm_ne_top : forall s in C, m s != ∞
) {s t : Set α} (hs : s in C) …
· 使用引理 `MeasureTheory.isSetRing_measurableCylinders`：isSetRing_measurableCylinde
rs : IsSetRing (measurableCylinders α)
· 使用引理 `MeasureTheory.projectiveFamilyContent_ne_top`：projectiveFamilyContent_ne
_top [forall J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) : proj
ectiveFamilyContent hP s != ∞
-/
lemma projectiveFamilyContent_sdiff_of_subset [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) (hs : s ∈ measurableCylinders α)
    (ht : t ∈ measurableCylinders α) (hts : t ⊆ s) :
    projectiveFamilyContent hP (s \ t)
      = projectiveFamilyContent hP s - projectiveFamilyContent hP t :=
  addContent_sdiff_of_ne_top (projectiveFamilyContent hP) isSetRing_measurableCylinders
    (fun _ _ ↦ projectiveFamilyContent_ne_top hP) hs ht hts

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff_of_subset := projectiveFamilyContent_sdiff_of_subset

end ProjectiveFamilyContent

end MeasureTheory

