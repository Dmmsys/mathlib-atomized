/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Semivariation

/-!
# Product of vector measures

Given two vector measures, we define their product `μ.prod ν B` as the vector measure assigning
to a measurable product `s × t` the mass `B (μ s) (ν t)`, if such a vector measure exists.
We show that it exists when either `μ` or `ν` has finite variation.

The API is modelled on the one for the product of positive measures.
-/

public section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {ι X Y E F G H I J : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup I] [NormedSpace ℝ I]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  {μ : VectorMeasure X E} {ν : VectorMeasure Y F} {B : E →L[ℝ] F →L[ℝ] G}

namespace MeasureTheory.VectorMeasure

/-- Two vector measures `μ` and `ν` have a product with respect to `B` if there exists a
measure giving mass `B (μ s) (ν t)` to any measurable product set `s × t`.
This is satisfied whenever `μ` or `ν` has finite variation. -/
/-
**MeasureTheory.VectorMeasure.HasProd** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory
.VectorMeasure`。
形式化陈述：{X : Type u_2} →   {Y : Type u_3} →     {E : Type u_4} →       {F : Type u
_5} →         {G : Type u_6} →           {mX : MeasurableSpace X} →             
{mY : MeasurableSpace Y} →               [inst : NormedAddCommGroup E] →        
         [inst_1 : NormedSpace ℝ E] →                   [inst_2 : NormedAddCommG
roup F] →                     [inst_3 : NormedSpace ℝ F] →                      
 [inst_4 : NormedAddCommGroup G] →                         [inst_5 : NormedSpace
 ℝ G] →                           MeasureTheory.VectorMeasure X E → MeasureTheor
y.VectorMeasure Y F → (E →L[ℝ] F →L[ℝ] G) → Prop
参数：E →L[ℝ] F →L[ℝ] G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vector measures `μ` and `ν` have a product with respect to `B` if there exis
ts a
measure giving mass `B (μ s) (ν t)` to any measurable product set `s × t`.
This is satisfied whenever `μ` or `ν` has finite variation.
-/
class HasProd (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) : Prop where
  exists_prod : ∃ ρ : VectorMeasure (X × Y) G, ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)

/-- The product of two vector measures `μ` and `ν` with respect to a continuous bilinear map `B`,
giving mass `B (μ s) (ν t)` to any measurable product set `s × t`.
If such a measure does not exist, we use the junk value `0`. -/
/-
**MeasureTheory.VectorMeasure.prod** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vect
orMeasure`。
形式化陈述：prod (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E ->L[Real] F ->
L[Real] G) : VectorMeasure (X × Y) G
参数：μ : VectorMeasure X E；ν : VectorMeasure Y F；B : E ->L[Real] F ->L[Real] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.HasProd.exists_prod`：∀ {X : Type u_2} {Y : T
ype u_3} {E : Type u_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X}  
 {mY : MeasurableSpace Y} {inst : Nor…

--- 原说明 ---
The product of two vector measures `μ` and `ν` with respect to a continuous bili
near map `B`,
giving mass `B (μ s) (ν t)` to any measurable product set `s × t`.
If such a measure does not exist, we use the junk value `0`.
-/
noncomputable def prod (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure (X × Y) G :=
  open scoped Classical in if h : HasProd μ ν B then h.exists_prod.choose else 0
/-
**MeasureTheory.VectorMeasure.prod_eq_zero_of_not_hasProd** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：prod_eq_zero_of_not_hasProd (h : ¬HasProd μ ν B) : μ.prod ν B = 0
参数：h : ¬HasProd μ ν B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma prod_eq_zero_of_not_hasProd (h : ¬HasProd μ ν B) :
    μ.prod ν B = 0 := by
  grind [HasProd, prod]
/-
**MeasureTheory.VectorMeasure.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.VectorMeasure`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} {mX : MeasurableSpace X}   {mY : MeasurableSpace Y} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : Norm
edSpace ℝ F] [inst_4 : NormedAddCommGroup G] [inst_5 : NormedSpace ℝ G]   {μ : M
easureTheory.VectorMeasure X E} {ν : MeasureTheory.VectorMeasure Y F} {B : E →L[
ℝ] F →L[ℝ] G}   [h : μ.HasProd ν B] {s : Set X} {t : Set Y}, (μ.prod ν B) (s ×ˢ 
t) = (B (μ s)) (ν t)
参数：μ.prod ν B；s ×ˢ t；B (μ s)；ν t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `MeasureTheory.VectorMeasure.HasProd.exists_prod`：∀ {X : Type u_2} {Y : T
ype u_3} {E : Type u_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X}  
 {mY : MeasurableSpace Y} {inst : Nor…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
（共 32 条，此处仅展示前 30 条）
-/
@[simp] lemma prod_apply [h : HasProd μ ν B] {s : Set X} {t : Set Y} :
    μ.prod ν B (s ×ˢ t) = B (μ s) (ν t) := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero, _root_.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h] using h.exists_prod.choose_spec s t h's h't
/-
**MeasureTheory.VectorMeasure.HasProd.flip** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure.HasProd`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_
6} {mX : MeasurableSpace X}   {mY : MeasurableSpace Y} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : Norm
edSpace ℝ F] [inst_4 : NormedAddCommGroup G] [inst_5 : NormedSpace ℝ G]   {μ : M
easureTheory.VectorMeasure X E} {ν : MeasureTheory.VectorMeasure Y F} {B : E →L[
ℝ] F →L[ℝ] G} [μ.HasProd ν B],   ν.HasProd μ B.flip
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.preimage_swap_prod`：preimage_swap_prod (s : Set α) (t : Set β) : Pro
d.swap ⁻¹' s ×ˢ t = t ×ˢ s
· 使用定理 `MeasureTheory.VectorMeasure.prod_apply`：∀ {X : Type u_2} {Y : Type u_3} 
{E : Type u_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X}   {mY : Me
asurableSpace Y} [inst : Nor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HasProd.flip [HasProd μ ν B] : HasProd ν μ B.flip where
  exists_prod := by
    refine ⟨(μ.prod ν B).map Prod.swap, fun s t hs ht ↦ ?_⟩
    rw [map_apply _ (by fun_prop) (hs.prod ht)]
    simp
/-
**MeasureTheory.VectorMeasure.hasProd_flip_iff** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：hasProd_flip_iff : HasProd ν μ B.flip ↔ HasProd μ ν B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.flip_flip`：flip_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 : f.flip.flip = f
· 使用定理 `MeasureTheory.VectorMeasure.HasProd.flip`：∀ {X : Type u_2} {Y : Type u_3
} {E : Type u_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X}   {mY : 
MeasurableSpace Y} [inst : Nor…
-/
lemma hasProd_flip_iff : HasProd ν μ B.flip ↔ HasProd μ ν B :=
  ⟨fun h ↦ by simpa using HasProd.flip (μ := ν) (ν := μ) (B := B.flip), fun h ↦ HasProd.flip⟩

omit [NormedSpace ℝ F] in
/-- If `ν` is a vector measure, and `s ⊆ X × Y` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
a strongly measurable function. -/
/-
**MeasureTheory.VectorMeasure.stronglyMeasurable_vectorMeasure_prodMk_left** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)} (hs : Measu
rableSet s) : StronglyMeasurable fun x => ν (Prod.mk x ⁻¹' s)
参数：X × Y；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
· 使用定理 `Set.mk_preimage_prod_right_eq_if`：mk_preimage_prod_right_eq_if [Decidabl
ePred (· in s)] : Prod.mk a ⁻¹' s ×ˢ t = if a in s then t else ∅
· 使用定理 `MeasureTheory.VectorMeasure.of_if`：of_if {ι : Type*} {x : ι} {B : Set ι}
 {A : Set α} [Decidable (x in B)] : v (if x in B then A else ∅) = indicator B (f
un _ => v A) x
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.VectorMeasure.of_compl`：of_compl {M : Type*} [AddCommGroup
 M] [TopologicalSpace M] [T2Space M] {v : VectorMeasure α M} {A : Set α} (hA : M
easurableSet A) : v Aᶜ = v…
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `MeasureTheory.VectorMeasure.hasSum_of_disjoint_iUnion`：hasSum_of_disjoin
t_iUnion (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : 
HasSum (fun i => v (f i)) (v (⋃ i, f i))
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `MeasureTheory.StronglyMeasurable.hasSum`：∀ {X : Type u_4} {E : Type u_5}
 {ι : Type u_6} [inst : MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 
: TopologicalSpace E] [Contin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α

--- 原说明 ---
If `ν` is a vector measure, and `s ⊆ X × Y` is measurable, then `x ↦ ν { y | (x,
 y) ∈ s }` is
a strongly measurable function.
-/
theorem stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)}
    (hs : MeasurableSet s) : StronglyMeasurable fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, of_if] using stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i ↦ ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i ↦ measurable_prodMk_left (hfm i), hfd.mono fun _ _ ↦ .preimage _]
    exact StronglyMeasurable.hasSum ihf this

omit [NormedSpace ℝ E] in
/-
**MeasureTheory.VectorMeasure.integrable_vectorMeasure_prodMk_left** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integrable_vectorMeasure_prodMk_left [IsFiniteMeasure μ.variation] {s : Se
t (X × Y)} (hs : MeasurableSet s) : μ.Integrable fun x => ν (Prod.mk x ⁻¹' s)
参数：X × Y；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.of_bound`：∀ {α : Type u_1} {E : Type u_5} {mα :
 MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.VectorMeasure.stronglyMeasurable_vectorMeasure_prodMk_left
`：stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)} (hs : Measurabl
eSet s) : StronglyMeasurable fun x => ν (Prod.mk x ⁻¹' s)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.VectorMeasure.norm_apply_le_bound`：norm_apply_le_bound : ‖
μ s‖ <= μ.bound
-/
theorem integrable_vectorMeasure_prodMk_left [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.Integrable fun x ↦ ν (Prod.mk x ⁻¹' s) := by
  refine Integrable.of_bound (μ := μ.variation) ?_ ν.bound ?_
  · exact (stronglyMeasurable_vectorMeasure_prodMk_left hs).aestronglyMeasurable
  · exact Eventually.of_forall (fun x ↦ norm_apply_le_bound)

/-- The product of two vector measures when the first one has finite variation, obtained by
integrating the measure of the fibers, as in the definition of the product of positive measures.
*Do not use*: This is only used to instantiate the typeclass `HasProd`. Instead, use `μ.prod ν B`,
which uses the typeclass instance. -/
/-
**MeasureTheory.VectorMeasure.prodOfIsFiniteMeasureLeft** 是 Mathlib 中的一个定义，位于命名空
间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two vector measures when the first one has finite variation, obta
ined by
integrating the measure of the fibers, as in the definition of the product of po
sitive measures.
*Do not use*: This is only used to instantiate the typeclass `HasProd`. Instead,
 use `μ.prod ν B`,
which uses the typeclass instance.
-/
private noncomputable def prodOfIsFiniteMeasureLeft
    (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G)
    [IsFiniteMeasure μ.variation] :
    VectorMeasure (X × Y) G where
  measureOf' s := open scoped Classical in
    if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion,
      HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset ℕ) : ∑ y ∈ a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y ∈ a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum _ (fun i hi ↦ integrable_vectorMeasure_prodMk_left (f_meas i))]
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x ↦ ν.bound)
    · apply Eventually.of_forall (fun a ↦ ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi ↦ ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply norm_apply_le_bound
      · exact fun i hi j hj hij ↦ (f_disj hij).preimage _
      · exact fun i hi ↦ measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i ↦ measurable_prodMk_left (f_meas i)
      · exact fun i j hij ↦ (f_disj hij).preimage _
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace G] [IsFiniteMeasure μ.variation] : HasProd μ ν B where
  exists_prod := by
    classical
    refine ⟨prodOfIsFiniteMeasureLeft μ ν B, fun s t hs ht ↦ ?_⟩
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, hs, restrict_apply]
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace G] [h : IsFiniteMeasure ν.variation] : HasProd μ ν B :=
  hasProd_flip_iff.1 inferInstance
/-
**MeasureTheory.VectorMeasure.prod_eq_of_forall_apply_prod** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：prod_eq_of_forall_apply_prod {ρ : VectorMeasure (X × Y) G} (hρ : forall (s
 : Set X) (t : Set Y), MeasurableSet s -> MeasurableSet t -> ρ (s ×ˢ t) = B (μ s
) (ν t)) : μ.prod ν B = ρ
参数：X × Y；hρ : forall (s : Set X) (t : Set Y), MeasurableSet s -> MeasurableSet t
 -> ρ (s ×ˢ t) = B (μ s) (ν t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext_of_generateFrom`：ext_of_generateFrom {M 
: Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] {X : Type*} {mX : Mea
surableSpace X} {μ ν : VectorMeasure …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.prod_apply`：∀ {X : Type u_2} {Y : Type u_3} 
{E : Type u_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X}   {mY : Me
asurableSpace Y} [inst : Nor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma prod_eq_of_forall_apply_prod {ρ : VectorMeasure (X × Y) G} (hρ : ∀ (s : Set X) (t : Set Y),
    MeasurableSet s → MeasurableSet t → ρ (s ×ˢ t) = B (μ s) (ν t)) :
    μ.prod ν B = ρ := by
  have : HasProd μ ν B := ⟨ρ, hρ⟩
  apply ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← univ_prod_univ, hρ _ _ MeasurableSet.univ MeasurableSet.univ, prod_apply]
  · rintro - ⟨s, hs, t, ht, rfl⟩
    rw [prod_apply, hρ _ _ hs ht]
/-
**MeasureTheory.VectorMeasure.prod_apply_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：prod_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation] {s 
: Set (X × Y)} (hs : MeasurableSet s) : μ.prod ν B s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s)
 ∂[B.flip; μ]
参数：X × Y；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.VectorMeasure.prod_eq_of_forall_apply_prod`：prod_eq_of_for
all_apply_prod {ρ : VectorMeasure (X × Y) G} (hρ : forall (s : Set X) (t : Set Y
), MeasurableSet s -> MeasurableSet t -> ρ (s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mk_preimage_prod_right_eq_if`：mk_preimage_prod_right_eq_if [Decidabl
ePred (· in s)] : Prod.mk a ⁻¹' s ×ˢ t = if a in s then t else ∅
· 使用定理 `MeasureTheory.VectorMeasure.of_if`：of_if {ι : Type*} {x : ι} {B : Set ι}
 {A : Set α} [Decidable (x in B)] : v (if x in B then A else ∅) = indicator B (f
un _ => v A) x
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator`：integral_indicator (hs :
 MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.integral_const`：integral_const [CompleteSpac
e G] [IsFiniteMeasure μ.variation] (c : E) : ∫ᵛ _ : X, c ∂[B; μ] = B c (μ univ)
· 使用定理 `MeasureTheory.VectorMeasure.instIsFiniteMeasureVariationRestrict`：∀ {X :
 Type u_1} {V : Type u_2} {mX : MeasurableSpace X} [inst : TopologicalSpace V] [
inst_1 : ENormedAddCommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] := by
  have : μ.prod ν B = prodOfIsFiniteMeasureLeft μ ν B := by
    classical
    apply prod_eq_of_forall_apply_prod (fun s t hs ht ↦ ?_)
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, restrict_apply, hs]
  rw [this]
  simp [prodOfIsFiniteMeasureLeft, hs]
/-
**MeasureTheory.VectorMeasure.prod_flip_apply_eq_integral** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：prod_flip_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation
] {B : F ->L[Real] E ->L[Real] G} {s : Set (X × Y)} (hs : MeasurableSet s) : μ.p
rod ν B.flip s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B; μ]
参数：X × Y；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.prod_apply_eq_integral`：prod_apply_eq_integr
al [CompleteSpace G] [IsFiniteMeasure μ.variation] {s : Set (X × Y)} (hs : Measu
rableSet s) : μ.prod ν B s = ∫ᵛ x, ν (Pr…
· 使用定理 `ContinuousLinearMap.flip_flip`：flip_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 : f.flip.flip = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_flip_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {B : F →L[ℝ] E →L[ℝ] G} {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B.flip s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B; μ] := by
  simp [prod_apply_eq_integral hs]
/-
**MeasureTheory.VectorMeasure.variation_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：variation_prod_le [CompleteSpace G] [IsFiniteMeasure μ.variation] [SFinite
 ν.variation] : (μ.prod ν B).variation <= ‖B‖ₑ • μ.variation.prod ν.variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.prod_apply_eq_integral`：prod_apply_eq_integr
al [CompleteSpace G] [IsFiniteMeasure μ.variation] {s : Set (X × Y)} (hs : Measu
rableSet s) : μ.prod ν B s = ∫ᵛ x, ν (Pr…
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.VectorMeasure.enorm_integral_le_lintegral_enorm`：enorm_int
egral_le_lintegral_enorm : ‖∫ᵛ a, f a ∂[B; μ]‖ₑ <= ‖B‖ₑ * ∫⁻ a, ‖f a‖ₑ ∂μ.variat
ion
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ContinuousLinearMap.opENorm_flip`：opENorm_flip (f : E ->SL[σ₁₃] F ->SL[σ
₂₃] G) : ‖f.flip‖ₑ = ‖f‖ₑ
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
-/
lemma variation_prod_le [CompleteSpace G] [IsFiniteMeasure μ.variation] [SFinite ν.variation] :
    (μ.prod ν B).variation ≤ ‖B‖ₑ • μ.variation.prod ν.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  rw [prod_apply_eq_integral hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs]
  grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_flip,
    enorm_measure_le_variation]
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace G] [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation] :
    IsFiniteMeasure (μ.prod ν B).variation := by
  have : IsFiniteMeasure (‖B‖ₑ • μ.variation.prod ν.variation) := by
    simp only [enorm_eq_nnnorm, Measure.coe_nnreal_smul]
    infer_instance
  exact isFiniteMeasure_of_le _ variation_prod_le

end MeasureTheory.VectorMeasure

