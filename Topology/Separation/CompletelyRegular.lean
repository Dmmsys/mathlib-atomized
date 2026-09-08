/-
Copyright (c) 2023 Matias Heikkilä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matias Heikkilä
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.Real.Cardinality

import Mathlib.Topology.Algebra.Indicator

/-!
# Completely regular topological spaces.

This file defines `CompletelyRegularSpace` and `T35Space`.

## Main definitions

* `CompletelyRegularSpace`: A completely regular space `X` is such that each closed set `K ⊆ X`
  and a point `x ∈ Kᶜ`, there is a continuous function `f` from `X` to the unit interval, so that
  `f x = 0` and `f k = 1` for all `k ∈ K`. A completely regular space is a regular space, and a
  normal space is a completely regular space.
* `T35Space`: A T₃.₅ space is a completely regular space that is also T₀. A T₃.₅ space is a T₃
  space and a T₄ space is a T₃.₅ space.

## Main results

### Completely regular spaces

* `CompletelyRegularSpace.regularSpace`: A completely regular space is a regular space.
* `NormalSpace.completelyRegularSpace`: A normal R0 space is a completely regular space.

### T₃.₅ spaces

* `T35Space.instT3Space`: A T₃.₅ space is a T₃ space.
* `T4Space.instT35Space`: A T₄ space is a T₃.₅ space.

## Implementation notes

The present definition `CompletelyRegularSpace` is a slight modification of the one given in
[russell1974]. There it's assumed that any point `x ∈ Kᶜ` is separated from the closed set `K` by a
continuous *real*-valued function `f` (as opposed to `f` being unit-interval-valued). This can be
converted to the present definition by replacing a real-valued `f` by `h ∘ g ∘ f`, with
`g : x ↦ max(x, 0)` and `h : x ↦ min(x, 1)`. Some sources (e.g. [russell1974]) also assume that a
completely regular space is T₁. Here a completely regular space that is also T₁ is called a T₃.₅
space.

## References

* [Russell C. Walker, *The Stone-Čech Compactification*][russell1974]
-/

public section

universe u v

noncomputable section

open Set Topology Filter unitInterval

variable {X : Type u} [TopologicalSpace X]

/-- A space is completely regular if points can be separated from closed sets via
  continuous functions to the unit interval. -/
@[mk_iff]
/-
**CompletelyRegularSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space is completely regular if points can be separated from closed sets via
  continuous functions to the unit interval.
-/
class CompletelyRegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  completely_regular : ∀ (x : X), ∀ K : Set X, IsClosed K → x ∉ K →
    ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 K
/-
**completelyRegularSpace_iff_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completelyRegularSpace_iff_isOpen : CompletelyRegularSpace X ↔ forall (x :
 X), forall K : Set X, IsOpen K -> x in K -> exists f : X -> I, Continuous f ∧ f
 x = 0 ∧ EqOn f 1 Kᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma completelyRegularSpace_iff_isOpen : CompletelyRegularSpace X ↔
    ∀ (x : X), ∀ K : Set X, IsOpen K → x ∈ K →
      ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 Kᶜ := by
  conv_lhs => tactic =>
    simp_rw +singlePass [completelyRegularSpace_iff, compl_surjective.forall, isClosed_compl_iff,
      mem_compl_iff, not_not]
/-
**CompletelyRegularSpace.completely_regular_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompletelyRegularSpace.completely_regular_isOpen [CompletelyRegularSpace X
] : forall (x : X), forall K : Set X, IsOpen K -> x in K -> exists f : X -> I, C
ontinuous f ∧ f x = 0 ∧ EqOn f 1 Kᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `completelyRegularSpace_iff_isOpen`：completelyRegularSpace_iff_isOpen : C
ompletelyRegularSpace X ↔ forall (x : X), forall K : Set X, IsOpen K -> x in K -
> exists f : X -> I, Co…
-/
lemma CompletelyRegularSpace.completely_regular_isOpen [CompletelyRegularSpace X] :
    ∀ (x : X), ∀ K : Set X, IsOpen K → x ∈ K →
      ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 Kᶜ :=
  completelyRegularSpace_iff_isOpen.mp inferInstance
/-
**CompletelyRegularSpace.instRegularSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompletelyRegularSpace.instRegularSpace [CompletelyRegularSpace X] : Regul
arSpace X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `regularSpace_iff`：∀ (X : Type u) [inst : TopologicalSpace X],   RegularS
pace X ↔ ∀ {s : Set X} {a : X}, IsClosed s → a ∉ s → Disjoint (nhdsSet s) (nhds 
a)
· 使用定理 `CompletelyRegularSpace.completely_regular`：∀ {X : Type u} {inst : Topolo
gicalSpace X} [self : CompletelyRegularSpace X] (x : X) (K : Set X),   IsClosed 
K → x ∉ K → ∃ f, Continuous f ∧…
· 使用引理 `Filter.disjoint_of_map`：disjoint_of_map {α β : Type*} {F G : Filter α} {
f : α -> β} (h : Disjoint (map f F) (map f G)) : Disjoint F G
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用引理 `Continuous.tendsto_nhdsSet_nhds`：Continuous.tendsto_nhdsSet_nhds {b : β}
 {f : α -> β} (h : Continuous f) (h' : EqOn f (fun _ => b) s) : Tendsto f (𝓝ˢ s)
 (𝓝 b)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_nhds_nhds`：disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint 
(𝓝 x) (𝓝 y) ↔ x != y
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance CompletelyRegularSpace.instRegularSpace [CompletelyRegularSpace X] :
    RegularSpace X := by
  rw [regularSpace_iff]
  intro s a hs ha
  obtain ⟨f, cf, hf, hhf⟩ := CompletelyRegularSpace.completely_regular a s hs ha
  apply disjoint_of_map (f := f)
  apply Disjoint.mono (cf.tendsto_nhdsSet_nhds hhf) cf.continuousAt
  exact disjoint_nhds_nhds.mpr (hf.symm ▸ zero_ne_one).symm
/-
**NormalSpace.instCompletelyRegularSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormalSpace.instCompletelyRegularSpace [NormalSpace X] [R0Space X] : Compl
etelyRegularSpace X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completelyRegularSpace_iff`：∀ (X : Type u) [inst : TopologicalSpace X], 
  CompletelyRegularSpace X ↔ ∀ (x : X) (K : Set X), IsClosed K → x ∉ K → ∃ f, Co
ntinuous f ∧ f x…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Specializes.mem_closed`：Specializes.mem_closed (h : x ⤳ y) (hs : IsClose
d s) (hx : x in s) : y in s
· 使用定理 `Specializes.symm`：Specializes.symm (h : x ⤳ y) : y ⤳ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
instance NormalSpace.instCompletelyRegularSpace [NormalSpace X] [R0Space X] :
    CompletelyRegularSpace X := by
  rw [completelyRegularSpace_iff]
  intro x K hK hx
  have cx : IsClosed (closure {x}) := isClosed_closure
  have d : Disjoint (closure {x}) K := by
    rw [Set.disjoint_iff]
    intro a ⟨hax, haK⟩
    exact hx ((specializes_iff_mem_closure.mpr hax).symm.mem_closed hK haK)
  let ⟨⟨f, cf⟩, hfx, hfK, hficc⟩ := exists_continuous_zero_one_of_isClosed cx hK d
  let g : X → I := fun x => ⟨f x, hficc x⟩
  have cg : Continuous g := cf.subtype_mk hficc
  have hgx : g x = 0 := Subtype.ext (hfx (subset_closure (mem_singleton x)))
  have hgK : EqOn g 1 K := fun k hk => Subtype.ext (hfK hk)
  exact ⟨g, cg, hgx, hgK⟩
/-
**Topology.IsInducing.completelyRegularSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.completelyRegularSpace {Y : Type v} [TopologicalSpace 
Y] [CompletelyRegularSpace Y] {f : X -> Y} (hf : IsInducing f) : CompletelyRegul
arSpace X where completely_regular x K hK hxK
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `CompletelyRegularSpace.completely_regular`：∀ {X : Type u} {inst : Topolo
gicalSpace X} [self : CompletelyRegularSpace X] (x : X) (K : Set X),   IsClosed 
K → x ∉ K → ∃ f, Continuous f ∧…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Set.EqOn.comp_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s :
 Set α} {t : Set β} {f : α → β} {g₁ g₂ : β → γ},   Set.EqOn g₁ g₂ t → Set.MapsTo
 f s t → …
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
lemma Topology.IsInducing.completelyRegularSpace
    {Y : Type v} [TopologicalSpace Y] [CompletelyRegularSpace Y]
    {f : X → Y} (hf : IsInducing f) : CompletelyRegularSpace X where
  completely_regular x K hK hxK := by
    rw [hf.isClosed_iff] at hK
    obtain ⟨K, hK, rfl⟩ := hK
    rw [mem_preimage] at hxK
    obtain ⟨g, hcf, egfx, hgK⟩ := CompletelyRegularSpace.completely_regular _ _ hK hxK
    refine ⟨g ∘ f, hcf.comp hf.continuous, egfx, ?_⟩
    conv => arg 2; equals (1 : Y → ↥I) ∘ f => rfl
    exact hgK.comp_right <| mapsTo_preimage _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : X → Prop} [CompletelyRegularSpace X] : CompletelyRegularSpace (Subtype p) :=
  Topology.IsInducing.subtypeVal.completelyRegularSpace
/-
**completelyRegularSpace_induced** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completelyRegularSpace_induced {X Y : Type*} {t : TopologicalSpace Y} (ht 
: @CompletelyRegularSpace Y t) (f : X -> Y) : @CompletelyRegularSpace X (t.induc
ed f)
参数：ht : @CompletelyRegularSpace Y t；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.completelyRegularSpace`：Topology.IsInducing.complete
lyRegularSpace {Y : Type v} [TopologicalSpace Y] [CompletelyRegularSpace Y] {f :
 X -> Y} (hf : IsInducing f) : C…
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
-/
lemma completelyRegularSpace_induced
    {X Y : Type*} {t : TopologicalSpace Y} (ht : @CompletelyRegularSpace Y t)
    (f : X → Y) : @CompletelyRegularSpace X (t.induced f) :=
  @IsInducing.completelyRegularSpace _ (t.induced f) _ t _ _ (IsInducing.induced f)
/-
**completelyRegularSpace_iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completelyRegularSpace_iInf {ι X : Type*} {t : ι -> TopologicalSpace X} (h
t : forall i, @CompletelyRegularSpace X (t i)) : @CompletelyRegularSpace X (⨅ i,
 t i)
参数：ht : forall i, @CompletelyRegularSpace X (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `completelyRegularSpace_iff_isOpen`：completelyRegularSpace_iff_isOpen : C
ompletelyRegularSpace X ↔ forall (x : X), forall K : Set X, IsOpen K -> x in K -
> exists f : X -> I, Co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用引理 `CompletelyRegularSpace.completely_regular_isOpen`：CompletelyRegularSpace
.completely_regular_isOpen [CompletelyRegularSpace X] : forall (x : X), forall K
 : Set X, IsOpen K -> x in K -> exists…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Continuous.finset_sup`：Continuous.finset_sup (hs : forall i in s, Contin
uous (f i)) : Continuous (s.sup f)
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `LinearOrder.topologicalLattice`：∀ {L : Type u_1} [inst : TopologicalSpac
e L] [inst_1 : LinearOrder L] [OrderClosedTopology L], TopologicalLattice L
· 使用定理 `Subtype.instOrderClosedTopology`：∀ {α : Type u} [inst : TopologicalSpace
 α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {p : α → Prop},   OrderClo
sedTopology (Subtype …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_iInf_dom`：continuous_iInf_dom {t₁ : ι -> TopologicalSpace α} 
{t₂ : TopologicalSpace β} {i : ι} : Continuous[t₁ i, t₂] f -> Continuous[iInf t₁
, t₂] f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup_apply`：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [in
st : (b : β) → SemilatticeSup (C b)]   [inst_1 : (b : β) → OrderBot (C b)] (s : 
Finset…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma completelyRegularSpace_iInf {ι X : Type*} {t : ι → TopologicalSpace X}
    (ht : ∀ i, @CompletelyRegularSpace X (t i)) : @CompletelyRegularSpace X (⨅ i, t i) := by
  let := (⨅ i, t i) -- register this as default topological space to reduce `@`s
  rw [completelyRegularSpace_iff_isOpen]
  intro x K hK hxK
  simp_rw [← hK.mem_nhds_iff, nhds_iInf, mem_iInf, exists_finite_iff_finset,
    Finset.coe_sort_coe] at hxK; clear hK
  obtain ⟨I', V, hV, rfl⟩ := hxK
  simp only [mem_nhds_iff] at hV
  choose U hUV hU hxU using hV
  replace hU := fun (i : ↥I') =>
    @CompletelyRegularSpace.completely_regular_isOpen _ (t i) (ht i) x (U i) (hU i) (hxU i)
  clear hxU
  choose fs hfs hxfs hfsU using hU
  use I'.attach.sup fs
  constructorm* _ ∧ _
  · solve_by_elim [Continuous.finset_sup, continuous_iInf_dom]
  · simpa [show (0 : ↥I) = ⊥ from rfl] using hxfs
  · simp only [EqOn, Pi.one_apply, show (1 : ↥I) = ⊤ from rfl] at hfsU ⊢
    conv => equals ∀ x i, x ∈ (V i)ᶜ → ∃ b, fs b x = ⊤ => simp [Finset.sup_eq_top_iff]
    intro x i hxi
    specialize hfsU i (by tauto_set)
    exists i

set_option backward.isDefEq.respectTransparency false in
/-
**completelyRegularSpace_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completelyRegularSpace_inf {X : Type*} {t₁ t₂ : TopologicalSpace X} (ht₁ :
 @CompletelyRegularSpace X t₁) (ht₂ : @CompletelyRegularSpace X t₂) : @Completel
yRegularSpace X (t₁ ⊓ t₂)
参数：ht₁ : @CompletelyRegularSpace X t₁；ht₂ : @CompletelyRegularSpace X t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用引理 `completelyRegularSpace_iInf`：completelyRegularSpace_iInf {ι X : Type*} {
t : ι -> TopologicalSpace X} (ht : forall i, @CompletelyRegularSpace X (t i)) : 
@CompletelyRegula…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma completelyRegularSpace_inf {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (ht₁ : @CompletelyRegularSpace X t₁) (ht₂ : @CompletelyRegularSpace X t₂) :
    @CompletelyRegularSpace X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]; apply completelyRegularSpace_iInf; simp [*]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [t : Π (i : ι), TopologicalSpace (X i)]
    [ht : Π (i : ι), CompletelyRegularSpace (X i)] : CompletelyRegularSpace (Π i, X i) :=
  completelyRegularSpace_iInf (fun i => completelyRegularSpace_induced (ht i) _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [htX : CompletelyRegularSpace X] [htY : CompletelyRegularSpace Y] :
    CompletelyRegularSpace (X × Y) :=
  completelyRegularSpace_inf
    (completelyRegularSpace_induced htX _) ((completelyRegularSpace_induced htY _))
/-
**isInducing_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isInducing_stoneCechUnit [CompletelyRegularSpace X] : IsInducing (stoneCec
hUnit : X -> StoneCech X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isInducing_iff_nhds`：isInducing_iff_nhds : IsInducing f ↔ foral
l x, 𝓝 x = comap f (𝓝 (f x))
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_stoneCechUnit`：continuous_stoneCechUnit : Continuous (stoneCe
chUnit : α -> StoneCech α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CompletelyRegularSpace.completely_regular_isOpen`：CompletelyRegularSpace
.completely_regular_isOpen [CompletelyRegularSpace X] : forall (x : X), forall K
 : Set X, IsOpen K -> x in K -> exists…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用引理 `stoneCechExtend_stoneCechUnit`：stoneCechExtend_stoneCechUnit (a : α) : s
toneCechExtend hg (stoneCechUnit a) = g a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_stoneCechExtend`：continuous_stoneCechExtend : Continuous (sto
neCechExtend hg)
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
（共 38 条，此处仅展示前 30 条）
-/
lemma isInducing_stoneCechUnit [CompletelyRegularSpace X] :
    IsInducing (stoneCechUnit : X → StoneCech X) := by
  rw [isInducing_iff_nhds]
  intro x
  apply le_antisymm
  · rw [← map_le_iff_le_comap]; exact continuous_stoneCechUnit.continuousAt
  · simp_rw [le_nhds_iff, ((nhds_basis_opens _).comap _).mem_iff, and_assoc]
    intro U hxU hU
    obtain ⟨f, hf, efx, hfU⟩ :=
      CompletelyRegularSpace.completely_regular_isOpen x U hU hxU
    conv at hfU => equals Uᶜ ⊆ f ⁻¹' {1} => simp [EqOn, subset_def]
    rw [← compl_subset_comm, ← preimage_compl, ← stoneCechExtend_extends hf, preimage_comp] at hfU
    refine ⟨stoneCechExtend hf ⁻¹' {1}ᶜ, ?_,
      isOpen_compl_singleton.preimage (continuous_stoneCechExtend hf), hfU⟩
    rw [mem_preimage, stoneCechExtend_stoneCechUnit, efx, mem_compl_iff, mem_singleton_iff]
    simp
/-
**isDenseInducing_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDenseInducing_stoneCechUnit [CompletelyRegularSpace X] : IsDenseInducing
 (stoneCechUnit : X -> StoneCech X) where toIsInducing
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isInducing_stoneCechUnit`：isInducing_stoneCechUnit [CompletelyRegularSpa
ce X] : IsInducing (stoneCechUnit : X -> StoneCech X)
· 使用定理 `denseRange_stoneCechUnit`：denseRange_stoneCechUnit : DenseRange (stoneCe
chUnit : α -> StoneCech α)
-/
lemma isDenseInducing_stoneCechUnit [CompletelyRegularSpace X] :
    IsDenseInducing (stoneCechUnit : X → StoneCech X) where
  toIsInducing := isInducing_stoneCechUnit
  dense := denseRange_stoneCechUnit
/-
**completelyRegularSpace_iff_isInducing_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：completelyRegularSpace_iff_isInducing_stoneCechUnit : CompletelyRegularSpa
ce X ↔ IsInducing (stoneCechUnit : X -> StoneCech X) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isInducing_stoneCechUnit`：isInducing_stoneCechUnit [CompletelyRegularSpa
ce X] : IsInducing (stoneCechUnit : X -> StoneCech X)
· 使用引理 `Topology.IsInducing.completelyRegularSpace`：Topology.IsInducing.complete
lyRegularSpace {Y : Type v} [TopologicalSpace Y] [CompletelyRegularSpace Y] {f :
 X -> Y} (hf : IsInducing f) : C…
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `instCompactSpaceStoneCech`：∀ {α : Type u} [inst : TopologicalSpace α], C
ompactSpace (StoneCech α)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instT2SpaceStoneCech`：∀ {α : Type u} [inst : TopologicalSpace α], T2Spac
e (StoneCech α)
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
-/
lemma completelyRegularSpace_iff_isInducing_stoneCechUnit :
    CompletelyRegularSpace X ↔ IsInducing (stoneCechUnit : X → StoneCech X) where
  mp _ := isInducing_stoneCechUnit
  mpr hs := hs.completelyRegularSpace
/-
**CompletelyRegularSpace.of_isTopologicalBasis_clopens** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：CompletelyRegularSpace.of_isTopologicalBasis_clopens (h : TopologicalSpace
.IsTopologicalBasis {s : Set X | IsClopen s}) : CompletelyRegularSpace X where c
ompletely_regular x K hK hx
参数：h : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `IsClopen.continuous_indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : T
opologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α}   [inst
_2 : Zero β], IsClo…
· 使用定理 `IsClopen.compl`：IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
-/
theorem CompletelyRegularSpace.of_isTopologicalBasis_clopens
    (h : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}) :
    CompletelyRegularSpace X where
  completely_regular x K hK hx := by
    obtain ⟨s, hs, hx, hsK⟩ := h.exists_subset_of_mem_open hx hK.isOpen_compl
    refine ⟨sᶜ.indicator 1, ?_, by simpa, fun x hx ↦ indicator_of_mem ?_ _⟩
    · exact hs.compl.continuous_indicator continuous_const
    · exact (mem_compl_iff s x).mpr fun hs ↦ hsK hs hx

open TopologicalSpace Cardinal in
/-
**CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum**
 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continu
um [CompletelyRegularSpace X] (hX : Cardinal.mk X < continuum) : IsTopologicalBa
sis {s : Set X | IsClopen s}
参数：hX : Cardinal.mk X < continuum。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.lift_continuum`：lift_continuum : lift.{v} 𝔠 = 𝔠
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `Cardinal.lift_strictMono`：lift_strictMono : StrictMono lift
· 使用引理 `Cardinal.compl_nonempty_of_mk_lt_mk`：compl_nonempty_of_mk_lt_mk {S : Set
 α} (h : #S < #α) : Sᶜ.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.eq_1`：unitInterval = Set.Icc 0 1
· 使用定理 `Cardinal.mk_Icc_real`：mk_Icc_real {a b : Real} (h : a < b) : #(Icc a b) 
= 𝔠
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Subtype.instOrderClosedTopology`：∀ {α : Type u} [inst : TopologicalSpace
 α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {p : α → Prop},   OrderClo
sedTopology (Subtype …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
（共 39 条，此处仅展示前 30 条）
-/
theorem CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum
    [CompletelyRegularSpace X] (hX : Cardinal.mk X < continuum) :
    IsTopologicalBasis {s : Set X | IsClopen s} := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun x s ↦ IsClopen.isOpen s) (fun x s hxs hs ↦ ?_)
  choose f hf using completely_regular_isOpen x s hs hxs
  obtain ⟨hfc, hf₀, hf₁⟩ := hf
  let R := Set.range f
  have hR : lift.{u, 0} (Cardinal.mk R) < lift.{0, u} continuum := by
    simpa [R] using mk_range_le_lift.trans_lt (lift_strictMono hX)
  rw [lift_continuum, ← lift_continuum.{u, 0}, lift_lt, ← mk_Icc_real zero_lt_one, ← unitInterval]
    at hR
  obtain ⟨r, hr⟩ : ∃ r : I, r ∈ Rᶜ := compl_nonempty_of_mk_lt_mk hR
  have hr' : ∀ (x : X), f x ≠ r := by simpa [R] using hr
  have hrclopen : f ⁻¹' Iio r = f ⁻¹' Iic r := by
    ext; simp [le_iff_lt_or_eq, hr']
  refine ⟨f ⁻¹' Iio r, ⟨hrclopen ▸ isClosed_Iic.preimage hfc, isOpen_Iio.preimage hfc⟩, ?_, ?_⟩
  · simp [hf₀, hrclopen]
  · refine preimage_subset_iff.mpr (fun x ↦ ?_)
    contrapose; intro hxs
    simpa [hf₁ hxs] using le_one'

/-- A T₃.₅ space is a completely regular space that is also T₀. -/
@[mk_iff]
/-
**T35Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₃.₅ space is a completely regular space that is also T₀.
-/
class T35Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, CompletelyRegularSpace X
/-
**T35Space.instT3space** 是 Mathlib 中的一个定理，位于命名空间 `T35Space`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] [T35Space X], T3Space X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T35Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T
35Space X], T0Space X
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
-/
instance T35Space.instT3space [T35Space X] : T3Space X where
/-
**T4Space.instT35Space** 是 Mathlib 中的一个定理，位于命名空间 `T4Space`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] [T4Space X], T35Space X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T4Space.toNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self 
: T4Space X], NormalSpace X
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
-/
instance T4Space.instT35Space [T4Space X] : T35Space X where
/-
**Topology.IsEmbedding.t35Space** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.t35Space {Y : Type v} [TopologicalSpace Y] [T35Space 
Y] {f : X -> Y} (hf : IsEmbedding f) : T35Space X
参数：hf : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `T35Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T
35Space X], T0Space X
· 使用引理 `Topology.IsInducing.completelyRegularSpace`：Topology.IsInducing.complete
lyRegularSpace {Y : Type v} [TopologicalSpace Y] [CompletelyRegularSpace Y] {f :
 X -> Y} (hf : IsInducing f) : C…
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma Topology.IsEmbedding.t35Space
    {Y : Type v} [TopologicalSpace Y] [T35Space Y]
    {f : X → Y} (hf : IsEmbedding f) : T35Space X :=
  @T35Space.mk _ _ hf.t0Space hf.isInducing.completelyRegularSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : X → Prop} [T35Space X] : T35Space (Subtype p) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [t : Π (i : ι), TopologicalSpace (X i)]
    [ht : Π (i : ι), T35Space (X i)] : T35Space (Π i, X i) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [htX : T35Space X] [htY : T35Space Y] : T35Space (X × Y) where
/-
**separatesPoints_continuous_of_t35Space** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：separatesPoints_continuous_of_t35Space [T35Space X] : SeparatesPoints {f :
 X -> Real | Continuous f}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyRegularSpace.completely_regular`：∀ {X : Type u} {inst : Topolo
gicalSpace X} [self : CompletelyRegularSpace X] (x : X) (K : Set X),   IsClosed 
K → x ∉ K → ∃ f, Continuous f ∧…
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T35Space.instT3space`：∀ {X : Type u} [inst : TopologicalSpace X] [T35Spa
ce X], T3Space X
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma separatesPoints_continuous_of_t35Space [T35Space X] :
    SeparatesPoints {f : X → ℝ | Continuous f} := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨fun x ↦ f x, continuous_subtype_val.comp f_cont, by simp_all⟩
/-
**separatesPoints_continuous_of_t35Space_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：separatesPoints_continuous_of_t35Space_Icc [T35Space X] : SeparatesPoints 
{f : X -> I | Continuous f}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyRegularSpace.completely_regular`：∀ {X : Type u} {inst : Topolo
gicalSpace X} [self : CompletelyRegularSpace X] (x : X) (K : Set X),   IsClosed 
K → x ∉ K → ∃ f, Continuous f ∧…
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T35Space.instT3space`：∀ {X : Type u} [inst : TopologicalSpace X] [T35Spa
ce X], T3Space X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma separatesPoints_continuous_of_t35Space_Icc [T35Space X] :
    SeparatesPoints {f : X → I | Continuous f} := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨f, f_cont, by simp_all⟩
/-
**injective_stoneCechUnit_of_t35Space** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：injective_stoneCechUnit_of_t35Space [T35Space X] : Function.Injective (sto
neCechUnit : X -> StoneCech X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `separatesPoints_continuous_of_t35Space_Icc`：separatesPoints_continuous_o
f_t35Space_Icc [T35Space X] : SeparatesPoints {f : X -> I | Continuous f}
· 使用引理 `eq_if_stoneCechUnit_eq`：eq_if_stoneCechUnit_eq {a b : α} {f : α -> β} (h
cf : Continuous f) (h : stoneCechUnit a = stoneCechUnit b) : f a = f b
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma injective_stoneCechUnit_of_t35Space [T35Space X] :
    Function.Injective (stoneCechUnit : X → StoneCech X) := by
  intro a b hab
  contrapose hab
  obtain ⟨f, fc, fab⟩ := separatesPoints_continuous_of_t35Space_Icc hab
  exact fun q ↦ fab (eq_if_stoneCechUnit_eq fc q)
/-
**isEmbedding_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmbedding_stoneCechUnit [T35Space X] : IsEmbedding (stoneCechUnit : X ->
 StoneCech X) where toIsInducing
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isInducing_stoneCechUnit`：isInducing_stoneCechUnit [CompletelyRegularSpa
ce X] : IsInducing (stoneCechUnit : X -> StoneCech X)
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
· 使用引理 `injective_stoneCechUnit_of_t35Space`：injective_stoneCechUnit_of_t35Space
 [T35Space X] : Function.Injective (stoneCechUnit : X -> StoneCech X)
-/
lemma isEmbedding_stoneCechUnit [T35Space X] :
    IsEmbedding (stoneCechUnit : X → StoneCech X) where
  toIsInducing := isInducing_stoneCechUnit
  injective := injective_stoneCechUnit_of_t35Space
/-
**isDenseEmbedding_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDenseEmbedding_stoneCechUnit [T35Space X] : IsDenseEmbedding (stoneCechU
nit : X -> StoneCech X) where toIsDenseInducing
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isDenseInducing_stoneCechUnit`：isDenseInducing_stoneCechUnit [Completely
RegularSpace X] : IsDenseInducing (stoneCechUnit : X -> StoneCech X) where toIsI
nducing
· 使用定理 `T35Space.toCompletelyRegularSpace`：∀ {X : Type u} {inst : TopologicalSpa
ce X} [self : T35Space X], CompletelyRegularSpace X
· 使用引理 `injective_stoneCechUnit_of_t35Space`：injective_stoneCechUnit_of_t35Space
 [T35Space X] : Function.Injective (stoneCechUnit : X -> StoneCech X)
-/
lemma isDenseEmbedding_stoneCechUnit [T35Space X] :
    IsDenseEmbedding (stoneCechUnit : X → StoneCech X) where
  toIsDenseInducing := isDenseInducing_stoneCechUnit
  injective := injective_stoneCechUnit_of_t35Space
/-
**t35Space_iff_isEmbedding_stoneCechUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：t35Space_iff_isEmbedding_stoneCechUnit : T35Space X ↔ IsEmbedding (stoneCe
chUnit : X -> StoneCech X) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isEmbedding_stoneCechUnit`：isEmbedding_stoneCechUnit [T35Space X] : IsEm
bedding (stoneCechUnit : X -> StoneCech X) where toIsInducing
· 使用引理 `Topology.IsEmbedding.t35Space`：Topology.IsEmbedding.t35Space {Y : Type v
} [TopologicalSpace Y] [T35Space Y] {f : X -> Y} (hf : IsEmbedding f) : T35Space
 X
· 使用定理 `T4Space.instT35Space`：∀ {X : Type u} [inst : TopologicalSpace X] [T4Spac
e X], T35Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `instT2SpaceStoneCech`：∀ {α : Type u} [inst : TopologicalSpace α], T2Spac
e (StoneCech α)
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `instCompactSpaceStoneCech`：∀ {α : Type u} [inst : TopologicalSpace α], C
ompactSpace (StoneCech α)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
-/
lemma t35Space_iff_isEmbedding_stoneCechUnit :
    T35Space X ↔ IsEmbedding (stoneCechUnit : X → StoneCech X) where
  mp _ := isEmbedding_stoneCechUnit
  mpr hs := hs.t35Space
