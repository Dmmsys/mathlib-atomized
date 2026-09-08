/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Logic.Encodable.Pi
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.GromovHausdorffRealized
public import Mathlib.Topology.MetricSpace.Kuratowski

/-!
# Gromov-Hausdorff distance

This file defines the Gromov-Hausdorff distance on the space of nonempty compact metric spaces
up to isometry.

We introduce the space of all nonempty compact metric spaces, up to isometry,
called `GHSpace`, and endow it with a metric space structure. The distance,
known as the Gromov-Hausdorff distance, is defined as follows: given two
nonempty compact spaces `X` and `Y`, their distance is the minimum Hausdorff distance
between all possible isometric embeddings of `X` and `Y` in all metric spaces.
To define properly the Gromov-Hausdorff space, we consider the non-empty
compact subsets of `ℓ^∞(ℝ)` up to isometry, which is a well-defined type,
and define the distance as the infimum of the Hausdorff distance over all
embeddings in `ℓ^∞(ℝ)`. We prove that this coincides with the previous description,
as all separable metric spaces embed isometrically into `ℓ^∞(ℝ)`, through an
embedding called the Kuratowski embedding.
To prove that we have a distance, we should show that if spaces can be coupled
to be arbitrarily close, then they are isometric. More generally, the Gromov-Hausdorff
distance is realized, i.e., there is a coupling for which the Hausdorff distance
is exactly the Gromov-Hausdorff distance. This follows from a compactness
argument, essentially following from Arzela-Ascoli.

## Main results

We prove the most important properties of the Gromov-Hausdorff space: it is a polish space,
i.e., it is complete and second countable. We also prove the Gromov compactness criterion.

-/

@[expose] public section

noncomputable section

open scoped Topology ENNReal Cardinal
open Set Function TopologicalSpace Filter Metric Quotient Bornology
open BoundedContinuousFunction Nat Int kuratowskiEmbedding

open Sum (inl inr)

local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

attribute [local instance] metricSpaceSum

namespace GromovHausdorff

/-! In this section, we define the Gromov-Hausdorff space, denoted `GHSpace` as the quotient
of nonempty compact subsets of `ℓ^∞(ℝ)` by identifying isometric sets.
Using the Kuratowski embedding, we get a canonical map `toGHSpace` mapping any nonempty
compact type to `GHSpace`. -/
section GHSpace

set_option backward.privateInPublic true in
/-- Equivalence relation identifying two nonempty compact sets which are isometric -/
/-
**GromovHausdorff.IsometryRel** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence relation identifying two nonempty compact sets which are isometric
-/
private def IsometryRel (x : NonemptyCompacts ℓ_infty_ℝ) (y : NonemptyCompacts ℓ_infty_ℝ) : Prop :=
  Nonempty (x ≃ᵢ y)

set_option backward.privateInPublic true in
/-- This is indeed an equivalence relation -/
/-
**GromovHausdorff.equivalence_isometryRel** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausd
orff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is indeed an equivalence relation
-/
private theorem equivalence_isometryRel : Equivalence IsometryRel :=
  ⟨fun _ => Nonempty.intro (IsometryEquiv.refl _), fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/
/-
**GromovHausdorff.IsometryRel.setoid** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff.
IsometryRel`。
形式化陈述：Setoid (TopologicalSpace.NonemptyCompacts ↥(lp (fun n => ℝ) ⊤))
参数：TopologicalSpace.NonemptyCompacts ↥(lp (fun n => ℝ) ⊤)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.MetricSpace.GromovHausdorff.0.GromovHausdorff.
equivalence_isometryRel`：Equivalence GromovHausdorff.IsometryRel✝

--- 原说明 ---
setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ)
-/
instance IsometryRel.setoid : Setoid (NonemptyCompacts ℓ_infty_ℝ) :=
  Setoid.mk IsometryRel equivalence_isometryRel

/-- The Gromov-Hausdorff space -/
/-
**GromovHausdorff.GHSpace** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff`。
形式化陈述：GHSpace : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gromov-Hausdorff space
-/
def GHSpace : Type :=
  Quotient IsometryRel.setoid

/-- Map any nonempty compact type to `GHSpace` -/
/-
**GromovHausdorff.toGHSpace** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff`。
形式化陈述：toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GHS
pace
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map any nonempty compact type to `GHSpace`
-/
def toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GHSpace :=
  ⟦NonemptyCompacts.kuratowskiEmbedding X⟧
/-
**GromovHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited GHSpace :=
  ⟨Quot.mk _ ⟨⟨{0}, isCompact_singleton⟩, singleton_nonempty _⟩⟩

/-- A metric space representative of any abstract point in `GHSpace` -/
/-
**GromovHausdorff.GHSpace.Rep** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff.GHSpace
`。
形式化陈述：GromovHausdorff.GHSpace → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A metric space representative of any abstract point in `GHSpace`
-/
def GHSpace.Rep (p : GHSpace) : Type :=
  (Quotient.out p : NonemptyCompacts ℓ_infty_ℝ)
/-
**GromovHausdorff.eq_toGHSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdorff`。
形式化陈述：eq_toGHSpace_iff {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X
] {p : NonemptyCompacts ℓ_infty_Real} : ⟦p⟧ = toGHSpace X ↔ exists Ψ : X -> ℓ_in
fty_Real, Isometry Ψ ∧ range Ψ = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `kuratowskiEmbedding.isometry`：∀ (α : Type u) [inst : MetricSpace α] [ins
t_1 : TopologicalSpace.SeparableSpace α], Isometry (kuratowskiEmbedding α)
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `IsometryEquiv.range_eq_univ`：range_eq_univ (h : α ≃ᵢ β) : range h = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem eq_toGHSpace_iff {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {p : NonemptyCompacts ℓ_infty_ℝ} :
    ⟦p⟧ = toGHSpace X ↔ ∃ Ψ : X → ℓ_infty_ℝ, Isometry Ψ ∧ range Ψ = p := by
  simp only [toGHSpace, Quotient.eq]
  refine ⟨fun h => ?_, ?_⟩
  · rcases Setoid.symm h with ⟨e⟩
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange.trans e
    use fun x => f x, isometry_subtype_coe.comp f.isometry
    rw [range_comp', f.range_eq_univ, Set.image_univ, Subtype.range_coe]
  · rintro ⟨Ψ, ⟨isomΨ, rangeΨ⟩⟩
    have f :=
      ((kuratowskiEmbedding.isometry X).isometryEquivOnRange.symm.trans
          isomΨ.isometryEquivOnRange).symm
    have E : (range Ψ ≃ᵢ NonemptyCompacts.kuratowskiEmbedding X)
        = (p ≃ᵢ range (kuratowskiEmbedding X)) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rw [rangeΨ]; rfl
    exact ⟨cast E f⟩
/-
**GromovHausdorff.eq_toGHSpace** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdorff`。
形式化陈述：eq_toGHSpace {p : NonemptyCompacts ℓ_infty_Real} : ⟦p⟧ = toGHSpace p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GromovHausdorff.eq_toGHSpace_iff`：eq_toGHSpace_iff {X : Type u} [MetricS
pace X] [CompactSpace X] [Nonempty X] {p : NonemptyCompacts ℓ_infty_Real} : ⟦p⟧ 
= toGHSpace X ↔ exists…
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem eq_toGHSpace {p : NonemptyCompacts ℓ_infty_ℝ} : ⟦p⟧ = toGHSpace p :=
  eq_toGHSpace_iff.2 ⟨fun x => x, isometry_subtype_coe, Subtype.range_coe⟩

section

/-
**GromovHausdorff.repGHSpaceMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdor
ff`。
形式化陈述：repGHSpaceMetricSpace {p : GHSpace} : MetricSpace p.Rep
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance repGHSpaceMetricSpace {p : GHSpace} : MetricSpace p.Rep :=
  inferInstanceAs <| MetricSpace p.out
/-
**GromovHausdorff.rep_gHSpace_compactSpace** 是 Mathlib 中的一个实例，位于命名空间 `GromovHaus
dorff`。
形式化陈述：rep_gHSpace_compactSpace {p : GHSpace} : CompactSpace p.Rep
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rep_gHSpace_compactSpace {p : GHSpace} : CompactSpace p.Rep :=
  inferInstanceAs <| CompactSpace p.out
/-
**GromovHausdorff.rep_gHSpace_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorf
f`。
形式化陈述：rep_gHSpace_nonempty {p : GHSpace} : Nonempty p.Rep
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rep_gHSpace_nonempty {p : GHSpace} : Nonempty p.Rep :=
  inferInstanceAs <| Nonempty p.out

end

/-
**GromovHausdorff.GHSpace.toGHSpace_rep** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdor
ff.GHSpace`。
形式化陈述：∀ (p : GromovHausdorff.GHSpace), GromovHausdorff.toGHSpace p.Rep = p
参数：p : GromovHausdorff.GHSpace。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GromovHausdorff.eq_toGHSpace`：eq_toGHSpace {p : NonemptyCompacts ℓ_infty
_Real} : ⟦p⟧ = toGHSpace p
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
theorem GHSpace.toGHSpace_rep (p : GHSpace) : toGHSpace p.Rep = p := by
  change toGHSpace (Quot.out p : NonemptyCompacts ℓ_infty_ℝ) = p
  rw [← eq_toGHSpace]
  exact Quot.out_eq p

set_option backward.isDefEq.respectTransparency false in
/-- Two nonempty compact spaces have the same image in `GHSpace` if and only if they are
isometric. -/
/-
**GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv** 是 Mathlib 中的一个定理，位于
命名空间 `GromovHausdorff`。
形式化陈述：toGHSpace_eq_toGHSpace_iff_isometryEquiv {X : Type u} [MetricSpace X] [Com
pactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempt
y Y] : toGHSpace X = toGHSpace Y ↔ Nonempty (X ≃ᵢ Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `kuratowskiEmbedding.isometry`：∀ (α : Type u) [inst : MetricSpace α] [ins
t_1 : TopologicalSpace.SeparableSpace α], Isometry (kuratowskiEmbedding α)

--- 原说明 ---
Two nonempty compact spaces have the same image in `GHSpace` if and only if they
 are
isometric.
-/
theorem toGHSpace_eq_toGHSpace_iff_isometryEquiv {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    toGHSpace X = toGHSpace Y ↔ Nonempty (X ≃ᵢ Y) :=
  ⟨by
    simp only [toGHSpace]
    rw [Quotient.eq]
    rintro ⟨e⟩
    have I :
      (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) =
        (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rfl
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange
    have g := (kuratowskiEmbedding.isometry Y).isometryEquivOnRange.symm
    exact ⟨f.trans <| (cast I e).trans g⟩, by
    rintro ⟨e⟩
    simp only [toGHSpace]
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange.symm
    have g := (kuratowskiEmbedding.isometry Y).isometryEquivOnRange
    have I :
      (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) =
        (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rfl
    rw [Quotient.eq]
    exact ⟨cast I ((f.trans e).trans g)⟩⟩

/-- Distance on `GHSpace`: the distance between two nonempty compact spaces is the infimum
Hausdorff distance between isometric copies of the two spaces in a metric space. For the definition,
we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/
/-
**GromovHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Distance on `GHSpace`: the distance between two nonempty compact spaces is the i
nfimum
Hausdorff distance between isometric copies of the two spaces in a metric space.
 For the definition,
we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works f
or all spaces.
-/
instance : Dist GHSpace where
  dist x y := sInf <| (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ =>
    hausdorffDist (p.1 : Set ℓ_infty_ℝ) p.2) '' { a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y }

/-- The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff space. -/
/-
**GromovHausdorff.ghDist** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff`。
形式化陈述：ghDist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpac
e X] [MetricSpace Y] [Nonempty Y] [CompactSpace Y] : Real
参数：X : Type u；Y : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal 
by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff 
space.
-/
def ghDist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y]
    [Nonempty Y] [CompactSpace Y] : ℝ :=
  dist (toGHSpace X) (toGHSpace Y)
/-
**GromovHausdorff.dist_ghDist** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdorff`。
形式化陈述：dist_ghDist (p q : GHSpace) : dist p q = ghDist p.Rep q.Rep
参数：p q : GHSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GromovHausdorff.ghDist.eq_1`：∀ (X : Type u) (Y : Type v) [inst : MetricS
pace X] [inst_1 : Nonempty X] [inst_2 : CompactSpace X]   [inst_3 : MetricSpace 
Y] [inst_4 : None…
· 使用定理 `GromovHausdorff.GHSpace.toGHSpace_rep`：∀ (p : GromovHausdorff.GHSpace), 
GromovHausdorff.toGHSpace p.Rep = p
-/
theorem dist_ghDist (p q : GHSpace) : dist p q = ghDist p.Rep q.Rep := by
  rw [ghDist, p.toGHSpace_rep, q.toGHSpace_rep]

/-- The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance
of isometric copies of the spaces, in any metric space. -/
/-
**GromovHausdorff.ghDist_le_hausdorffDist** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausd
orff`。
形式化陈述：ghDist_le_hausdorffDist {X : Type u} [MetricSpace X] [CompactSpace X] [Non
empty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {γ : Type w}
 [MetricSpace γ] {Φ : X -> γ} {Ψ : Y -> γ} (ha : Isometry Φ) (hb : Isometry Ψ) :
 ghDist X Y <= hausdorffDist (range Φ) (range Ψ)
参数：ha : Isometry Φ；hb : Isometry Ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_mem_of_nonempty`：∀ (α : Type u_1) [Nonempty α], ∃ x, x ∈ Set.
univ
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.mem_union_right`：mem_union_right {x : α} {b : Set α} (a : Set α) : x
 in b -> x in a union b
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_isCompact_univ`：isCompact_iff_isCompact_univ : IsCompact s
 ↔ IsCompact (univ : Set s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Metric.hausdorffDist_image`：hausdorffDist_image (h : Isometry Φ) : hausd
orffDist (Φ '' s) (Φ '' t) = hausdorffDist s t
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.subtype`：∀ {X : Type u_2} [inst :
 TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] (s : Set X),   T
opologicalSpace.PseudoMetrizableSpac…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `kuratowskiEmbedding.isometry`：∀ (α : Type u) [inst : MetricSpace α] [ins
t_1 : TopologicalSpace.SeparableSpace α], Isometry (kuratowskiEmbedding α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `GromovHausdorff.eq_toGHSpace_iff`：eq_toGHSpace_iff {X : Type u} [MetricS
pace X] [CompactSpace X] [Nonempty X] {p : NonemptyCompacts ℓ_infty_Real} : ⟦p⟧ 
= toGHSpace X ↔ exists…
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `KuratowskiEmbedding.exists_isometric_embedding`：exists_isometric_embeddi
ng (α : Type u) [MetricSpace α] [SeparableSpace α] : exists f : α -> ℓ^∞(Nat, Re
al), Isometry f
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff dis
tance
of isometric copies of the spaces, in any metric space.
-/
theorem ghDist_le_hausdorffDist {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {γ : Type w} [MetricSpace γ]
    {Φ : X → γ} {Ψ : Y → γ} (ha : Isometry Φ) (hb : Isometry Ψ) :
    ghDist X Y ≤ hausdorffDist (range Φ) (range Ψ) := by
  /- For the proof, we want to embed `γ` in `ℓ^∞(ℝ)`, to say that the Hausdorff distance is realized
    in `ℓ^∞(ℝ)` and therefore bounded below by the Gromov-Hausdorff-distance. However, `γ` is not
    separable in general. We restrict to the union of the images of `X` and `Y` in `γ`, which is
    separable and therefore embeddable in `ℓ^∞(ℝ)`. -/
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  let s : Set γ := range Φ ∪ range Ψ
  let Φ' : X → s := fun y => ⟨Φ y, mem_union_left _ (mem_range_self _)⟩
  let Ψ' : Y → s := fun y => ⟨Ψ y, mem_union_right _ (mem_range_self _)⟩
  have IΦ' : Isometry Φ' := fun x y => ha x y
  have IΨ' : Isometry Ψ' := fun x y => hb x y
  have : IsCompact s := (isCompact_range ha.continuous).union (isCompact_range hb.continuous)
  have : CompactSpace s := ⟨isCompact_iff_isCompact_univ.1 ‹IsCompact s›⟩
  have ΦΦ' : Φ = Subtype.val ∘ Φ' := rfl
  have ΨΨ' : Ψ = Subtype.val ∘ Ψ' := rfl
  have : hausdorffDist (range Φ) (range Ψ) = hausdorffDist (range Φ') (range Ψ') := by
    rw [ΦΦ', ΨΨ', range_comp, range_comp]
    exact hausdorffDist_image isometry_subtype_coe
  rw [this]
  -- Embed `s` in `ℓ^∞(ℝ)` through its Kuratowski embedding
  let F := kuratowskiEmbedding s
  have : hausdorffDist (F '' range Φ') (F '' range Ψ') = hausdorffDist (range Φ') (range Ψ') :=
    hausdorffDist_image (kuratowskiEmbedding.isometry _)
  rw [← this]
  -- Let `A` and `B` be the images of `X` and `Y` under this embedding. They are in `ℓ^∞(ℝ)`, and
  -- their Hausdorff distance is the same as in the original space.
  let A : NonemptyCompacts ℓ_infty_ℝ :=
    ⟨⟨F '' range Φ',
        (isCompact_range IΦ'.continuous).image (kuratowskiEmbedding.isometry _).continuous⟩,
      (range_nonempty _).image _⟩
  let B : NonemptyCompacts ℓ_infty_ℝ :=
    ⟨⟨F '' range Ψ',
        (isCompact_range IΨ'.continuous).image (kuratowskiEmbedding.isometry _).continuous⟩,
      (range_nonempty _).image _⟩
  have AX : ⟦A⟧ = toGHSpace X := by
    rw [eq_toGHSpace_iff]
    exact ⟨fun x => F (Φ' x), (kuratowskiEmbedding.isometry _).comp IΦ', range_comp _ _⟩
  have BY : ⟦B⟧ = toGHSpace Y := by
    rw [eq_toGHSpace_iff]
    exact ⟨fun x => F (Ψ' x), (kuratowskiEmbedding.isometry _).comp IΨ', range_comp _ _⟩
  refine csInf_le ⟨0, ?_⟩ ?_
  · simp only [lowerBounds, mem_image, mem_prod, mem_ofPred_eq, Prod.exists, and_imp,
      forall_exists_index]
    intro t _ _ _ _ ht
    rw [← ht]
    exact hausdorffDist_nonneg
  apply (mem_image _ _ _).2
  exists (⟨A, B⟩ : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ)

/-- The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,
essentially by design. -/
/-
**GromovHausdorff.hausdorffDist_optimal** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdor
ff`。
形式化陈述：hausdorffDist_optimal {X : Type u} [MetricSpace X] [CompactSpace X] [Nonem
pty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : hausdorffDis
t (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) = ghDist X Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GromovHausdorff.eq_toGHSpace_iff`：eq_toGHSpace_iff {X : Type u} [MetricS
pace X] [CompactSpace X] [Nonempty X] {p : NonemptyCompacts ℓ_infty_Real} : ⟦p⟧ 
= toGHSpace X ↔ exists…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.exists_mem_of_nonempty`：∀ (α : Type u_1) [Nonempty α], ∃ x, x ∈ Set.
univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Metric.exists_dist_lt_of_hausdorffDist_lt`：exists_dist_lt_of_hausdorffDi
st_lt {r : Real} (h : x in s) (H : hausdorffDist s t < r) (fin : hausdorffEDist 
s t != ⊤) : exists y in t, dist…
· 使用定理 `Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded`：hausdorffEDist_ne_t
op_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty) (bs : IsBounded s)
 (bt : IsBounded t) : hausdorffEDist s t …
· 使用定理 `TopologicalSpace.NonemptyCompacts.nonempty`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), (↑s).Nonempty
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `TopologicalSpace.NonemptyCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.NonemptyCompacts α), IsCompact ↑s
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Isometry.diam_range`：diam_range (hf : Isometry f) : Metric.diam (range f
) = Metric.diam (univ : Set α)
· 使用定理 `Metric.diam_union`：diam_union {t : Set α} (xs : x in s) (yt : y in t) : 
diam (s union t) <= diam s + dist x y + diam t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
The optimal coupling constructed above realizes exactly the Gromov-Hausdorff dis
tance,
essentially by design.
-/
theorem hausdorffDist_optimal {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) = ghDist X Y := by
  inhabit X; inhabit Y
  /- we only need to check the inequality `≤`, as the other one follows from the previous lemma.
       As the Gromov-Hausdorff distance is an infimum, we need to check that the Hausdorff distance
       in the optimal coupling is smaller than the Hausdorff distance of any coupling.
       First, we check this for couplings which already have small Hausdorff distance: in this
       case, the induced "distance" on `X ⊕ Y` belongs to the candidates family introduced in the
       definition of the optimal coupling, and the conclusion follows from the optimality
       of the optimal coupling within this family.
    -/
  have A :
    ∀ p q : NonemptyCompacts ℓ_infty_ℝ,
      ⟦p⟧ = toGHSpace X →
        ⟦q⟧ = toGHSpace Y →
          hausdorffDist (p : Set ℓ_infty_ℝ) q < diam (univ : Set X) + 1 + diam (univ : Set Y) →
            hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤
              hausdorffDist (p : Set ℓ_infty_ℝ) q := by
    intro p q hp hq bound
    rcases eq_toGHSpace_iff.1 hp with ⟨Φ, ⟨Φisom, Φrange⟩⟩
    rcases eq_toGHSpace_iff.1 hq with ⟨Ψ, ⟨Ψisom, Ψrange⟩⟩
    have I : diam (range Φ ∪ range Ψ) ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by
      rcases exists_mem_of_nonempty X with ⟨xX, _⟩
      have : ∃ y ∈ range Ψ, dist (Φ xX) y < diam (univ : Set X) + 1 + diam (univ : Set Y) := by
        rw [Ψrange]
        have : Φ xX ∈ (p : Set _) := Φrange ▸ (mem_range_self _)
        exact
          exists_dist_lt_of_hausdorffDist_lt this bound
            (hausdorffEDist_ne_top_of_nonempty_of_bounded p.nonempty q.nonempty
              p.isCompact.isBounded q.isCompact.isBounded)
      rcases this with ⟨y, hy, dy⟩
      rcases mem_range.1 hy with ⟨z, hzy⟩
      rw [← hzy] at dy
      have DΦ : diam (range Φ) = diam (univ : Set X) := Φisom.diam_range
      have DΨ : diam (range Ψ) = diam (univ : Set Y) := Ψisom.diam_range
      calc
        diam (range Φ ∪ range Ψ) ≤ diam (range Φ) + dist (Φ xX) (Ψ z) + diam (range Ψ) :=
          diam_union (mem_range_self _) (mem_range_self _)
        _ ≤
            diam (univ : Set X) + (diam (univ : Set X) + 1 + diam (univ : Set Y)) +
              diam (univ : Set Y) := by
          rw [DΦ, DΨ]
          gcongr
        _ = 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := by ring
    let f : X ⊕ Y → ℓ_infty_ℝ := fun x =>
      match x with
      | inl y => Φ y
      | inr z => Ψ z
    let F : (X ⊕ Y) × (X ⊕ Y) → ℝ := fun p => dist (f p.1) (f p.2)
    -- check that the induced "distance" is a candidate
    have Fgood : F ∈ candidates X Y := by
      simp only [F, candidates, forall_const,
        dist_eq_zero, Set.mem_ofPred_eq]
      repeat' constructor
      · exact fun x y =>
          calc
            F (inl x, inl y) = dist (Φ x) (Φ y) := rfl
            _ = dist x y := Φisom.dist_eq x y
      · exact fun x y =>
          calc
            F (inr x, inr y) = dist (Ψ x) (Ψ y) := rfl
            _ = dist x y := Ψisom.dist_eq x y
      · exact fun x y => dist_comm _ _
      · exact fun x y z => dist_triangle _ _ _
      · exact fun x y =>
          calc
            F (x, y) ≤ diam (range Φ ∪ range Ψ) := by
              have A : ∀ z : X ⊕ Y, f z ∈ range Φ ∪ range Ψ := by
                intro z
                cases z
                · apply mem_union_left; apply mem_range_self
                · apply mem_union_right; apply mem_range_self
              refine dist_le_diam_of_mem ?_ (A _) (A _)
              rw [Φrange, Ψrange]
              exact (p ⊔ q).isCompact.isBounded
            _ ≤ 2 * diam (univ : Set X) + 1 + 2 * diam (univ : Set Y) := I
    let Fb := candidatesBOfCandidates F Fgood
    have : hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤ HD Fb :=
      hausdorffDist_optimal_le_HD _ _ (candidatesBOfCandidates_mem F Fgood)
    refine le_trans this (le_of_forall_gt_imp_ge_of_dense fun r hr => ?_)
    have I1 : ∀ x : X, (⨅ y, Fb (inl x, inr y)) ≤ r := by
      intro x
      have : f (inl x) ∈ (p : Set _) := Φrange ▸ (mem_range_self _)
      rcases exists_dist_lt_of_hausdorffDist_lt this hr
          (hausdorffEDist_ne_top_of_nonempty_of_bounded p.nonempty q.nonempty p.isCompact.isBounded
            q.isCompact.isBounded) with
        ⟨z, zq, hz⟩
      have : z ∈ range Ψ := by rwa [← Ψrange] at zq
      rcases mem_range.1 this with ⟨y, hy⟩
      calc
        (⨅ y, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :=
          ciInf_le (by simpa only [add_zero] using HD_below_aux1 0) y
        _ = dist (Φ x) (Ψ y) := rfl
        _ = dist (f (inl x)) z := by rw [hy]
        _ ≤ r := le_of_lt hz
    have I2 : ∀ y : Y, (⨅ x, Fb (inl x, inr y)) ≤ r := by
      intro y
      have : f (inr y) ∈ (q : Set _) := Ψrange ▸ (mem_range_self _)
      rcases exists_dist_lt_of_hausdorffDist_lt' this hr
          (hausdorffEDist_ne_top_of_nonempty_of_bounded p.nonempty q.nonempty p.isCompact.isBounded
            q.isCompact.isBounded) with
        ⟨z, zq, hz⟩
      have : z ∈ range Φ := by rwa [← Φrange] at zq
      rcases mem_range.1 this with ⟨x, hx⟩
      calc
        (⨅ x, Fb (inl x, inr y)) ≤ Fb (inl x, inr y) :=
          ciInf_le (by simpa only [add_zero] using HD_below_aux2 0) x
        _ = dist (Φ x) (Ψ y) := rfl
        _ = dist z (f (inr y)) := by rw [hx]
        _ ≤ r := le_of_lt hz
    simp only [HD, ciSup_le I1, ciSup_le I2, max_le_iff, and_self_iff]
  /- Get the same inequality for any coupling. If the coupling is quite good, the desired
    inequality has been proved above. If it is bad, then the inequality is obvious. -/
  have B :
    ∀ p q : NonemptyCompacts ℓ_infty_ℝ,
      ⟦p⟧ = toGHSpace X →
        ⟦q⟧ = toGHSpace Y →
          hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤
            hausdorffDist (p : Set ℓ_infty_ℝ) q := by
    intro p q hp hq
    by_cases h :
      hausdorffDist (p : Set ℓ_infty_ℝ) q < diam (univ : Set X) + 1 + diam (univ : Set Y)
    · exact A p q hp hq h
    · calc
        hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) ≤
            HD (candidatesBDist X Y) :=
          hausdorffDist_optimal_le_HD _ _ candidatesBDist_mem_candidatesB
        _ ≤ diam (univ : Set X) + 1 + diam (univ : Set Y) := HD_candidatesBDist_le
        _ ≤ hausdorffDist (p : Set ℓ_infty_ℝ) q := not_lt.1 h
  refine le_antisymm ?_ ?_
  · apply le_csInf
    · refine (Set.Nonempty.prod ?_ ?_).image _ <;> exact ⟨_, rfl⟩
    · rintro b ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
      exact B p q hp hq
  · exact ghDist_le_hausdorffDist (isometry_optimalGHInjl X Y) (isometry_optimalGHInjr X Y)

/-- The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding
the optimal coupling through its Kuratowski embedding. -/
/-
**GromovHausdorff.ghDist_eq_hausdorffDist** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausd
orff`。
形式化陈述：ghDist_eq_hausdorffDist (X : Type u) [MetricSpace X] [CompactSpace X] [Non
empty X] (Y : Type v) [MetricSpace Y] [CompactSpace Y] [Nonempty Y] : exists Φ :
 X -> ℓ_infty_Real, exists Ψ : Y -> ℓ_infty_Real, Isometry Φ ∧ Isometry Ψ ∧ ghDi
st X Y = hausdorffDist (range Φ) (range Ψ)
参数：X : Type u；Y : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `kuratowskiEmbedding.isometry`：∀ (α : Type u) [inst : MetricSpace α] [ins
t_1 : TopologicalSpace.SeparableSpace α], Isometry (kuratowskiEmbedding α)
· 使用定理 `GromovHausdorff.isometry_optimalGHInjl`：isometry_optimalGHInjl : Isometr
y (optimalGHInjl X Y)
· 使用定理 `GromovHausdorff.isometry_optimalGHInjr`：isometry_optimalGHInjr : Isometr
y (optimalGHInjr X Y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `GromovHausdorff.hausdorffDist_optimal`：hausdorffDist_optimal {X : Type u
} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y] [Co
mpactSpace Y] [Nonempty Y] …
· 使用定理 `Metric.hausdorffDist_image`：hausdorffDist_image (h : Isometry Φ) : hausd
orffDist (Φ '' s) (Φ '' t) = hausdorffDist s t

--- 原说明 ---
The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by
 embedding
the optimal coupling through its Kuratowski embedding.
-/
theorem ghDist_eq_hausdorffDist (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Y : Type v) [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    ∃ Φ : X → ℓ_infty_ℝ,
      ∃ Ψ : Y → ℓ_infty_ℝ,
        Isometry Φ ∧ Isometry Ψ ∧ ghDist X Y = hausdorffDist (range Φ) (range Ψ) := by
  let F := kuratowskiEmbedding (OptimalGHCoupling X Y)
  let Φ := F ∘ optimalGHInjl X Y
  let Ψ := F ∘ optimalGHInjr X Y
  refine ⟨Φ, Ψ, ?_, ?_, ?_⟩
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimalGHInjl X Y)
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimalGHInjr X Y)
  · rw [← image_univ, ← image_univ, image_comp F, image_univ, image_comp F (optimalGHInjr X Y),
      image_univ, ← hausdorffDist_optimal]
    exact (hausdorffDist_image (kuratowskiEmbedding.isometry _)).symm

/-- The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/
/-
**GromovHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff
 space.
-/
instance : MetricSpace GHSpace where
  dist := dist
  dist_self x := by
    rcases exists_rep x with ⟨y, hy⟩
    refine le_antisymm ?_ ?_
    · apply csInf_le
      · exact ⟨0, by rintro b ⟨⟨u, v⟩, -, rfl⟩; exact hausdorffDist_nonneg⟩
      · simp only [mem_image, mem_prod, mem_ofPred_eq, Prod.exists]
        exists y, y
        simpa only [and_self_iff, hausdorffDist_self_zero, eq_self_iff_true, and_true]
    · apply le_csInf
      · exact Set.Nonempty.image _ <| Set.Nonempty.prod ⟨y, hy⟩ ⟨y, hy⟩
      · rintro b ⟨⟨u, v⟩, -, rfl⟩; exact hausdorffDist_nonneg
  dist_comm x y := by
    have A :
      (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ =>
            hausdorffDist (p.1 : Set ℓ_infty_ℝ) p.2) ''
          { a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y } =
        (fun p : NonemptyCompacts ℓ_infty_ℝ × NonemptyCompacts ℓ_infty_ℝ =>
              hausdorffDist (p.1 : Set ℓ_infty_ℝ) p.2) ∘
            Prod.swap ''
          { a | ⟦a⟧ = x } ×ˢ { b | ⟦b⟧ = y } := by
      ext
      simp only [comp_apply, Prod.fst_swap, Prod.snd_swap, hausdorffDist_comm]
    simp only [dist, A, image_comp, image_swap_prod]
  eq_of_dist_eq_zero {x} {y} hxy := by
    /- To show that two spaces at zero distance are isometric,
       we argue that the distance is realized by some coupling.
        In this coupling, the two spaces are at zero Hausdorff distance,
        i.e., they coincide. Therefore, the original spaces are isometric. -/
    rcases ghDist_eq_hausdorffDist x.Rep y.Rep with ⟨Φ, Ψ, Φisom, Ψisom, DΦΨ⟩
    rw [← dist_ghDist, hxy] at DΦΨ
    have : range Φ = range Ψ := by
      have hΦ : IsCompact (range Φ) := isCompact_range Φisom.continuous
      have hΨ : IsCompact (range Ψ) := isCompact_range Ψisom.continuous
      apply (IsClosed.hausdorffDist_zero_iff_eq _ _ _).1 DΦΨ.symm
      · exact hΦ.isClosed
      · exact hΨ.isClosed
      · exact hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
          hΦ.isBounded hΨ.isBounded
    have T : (range Ψ ≃ᵢ y.Rep) = (range Φ ≃ᵢ y.Rep) := by rw [this]
    have eΨ := cast T Ψisom.isometryEquivOnRange.symm
    have e := Φisom.isometryEquivOnRange.trans eΨ
    rw [← x.toGHSpace_rep, ← y.toGHSpace_rep, toGHSpace_eq_toGHSpace_iff_isometryEquiv]
    exact ⟨e⟩
  dist_triangle x y z := by
    /- To show the triangular inequality between `X`, `Y` and `Z`,
        realize an optimal coupling between `X` and `Y` in a space `γ1`,
        and an optimal coupling between `Y` and `Z` in a space `γ2`.
        Then, glue these metric spaces along `Y`. We get a new space `γ`
        in which `X` and `Y` are optimally coupled, as well as `Y` and `Z`.
        Apply the triangle inequality for the Hausdorff distance in `γ`
        to conclude. -/
    let X := x.Rep
    let Y := y.Rep
    let Z := z.Rep
    let γ1 := OptimalGHCoupling X Y
    let γ2 := OptimalGHCoupling Y Z
    let Φ : Y → γ1 := optimalGHInjr X Y
    have hΦ : Isometry Φ := isometry_optimalGHInjr X Y
    let Ψ : Y → γ2 := optimalGHInjl Y Z
    have hΨ : Isometry Ψ := isometry_optimalGHInjl Y Z
    have Comm : toGlueL hΦ hΨ ∘ optimalGHInjr X Y = toGlueR hΦ hΨ ∘ optimalGHInjl Y Z :=
      toGlue_commute hΦ hΨ
    calc
      dist x z = dist (toGHSpace X) (toGHSpace Z) := by
        rw [x.toGHSpace_rep, z.toGHSpace_rep]
      _ ≤ hausdorffDist (range (toGlueL hΦ hΨ ∘ optimalGHInjl X Y))
            (range (toGlueR hΦ hΨ ∘ optimalGHInjr Y Z)) :=
        (ghDist_le_hausdorffDist ((toGlueL_isometry hΦ hΨ).comp (isometry_optimalGHInjl X Y))
          ((toGlueR_isometry hΦ hΨ).comp (isometry_optimalGHInjr Y Z)))
      _ ≤ hausdorffDist (range (toGlueL hΦ hΨ ∘ optimalGHInjl X Y))
              (range (toGlueL hΦ hΨ ∘ optimalGHInjr X Y)) +
            hausdorffDist (range (toGlueL hΦ hΨ ∘ optimalGHInjr X Y))
              (range (toGlueR hΦ hΨ ∘ optimalGHInjr Y Z)) := by
        refine hausdorffDist_triangle <| hausdorffEDist_ne_top_of_nonempty_of_bounded
          (range_nonempty _) (range_nonempty _) ?_ ?_
        · exact (isCompact_range (Isometry.continuous
            ((toGlueL_isometry hΦ hΨ).comp (isometry_optimalGHInjl X Y)))).isBounded
        · exact (isCompact_range (Isometry.continuous
            ((toGlueL_isometry hΦ hΨ).comp (isometry_optimalGHInjr X Y)))).isBounded
      _ = hausdorffDist (toGlueL hΦ hΨ '' range (optimalGHInjl X Y))
              (toGlueL hΦ hΨ '' range (optimalGHInjr X Y)) +
            hausdorffDist (toGlueR hΦ hΨ '' range (optimalGHInjl Y Z))
              (toGlueR hΦ hΨ '' range (optimalGHInjr Y Z)) := by
        simp only [← range_comp, Comm]
      _ = hausdorffDist (range (optimalGHInjl X Y)) (range (optimalGHInjr X Y)) +
            hausdorffDist (range (optimalGHInjl Y Z)) (range (optimalGHInjr Y Z)) := by
        rw [hausdorffDist_image (toGlueL_isometry hΦ hΨ),
          hausdorffDist_image (toGlueR_isometry hΦ hΨ)]
      _ = dist (toGHSpace X) (toGHSpace Y) + dist (toGHSpace Y) (toGHSpace Z) := by
        rw [hausdorffDist_optimal, hausdorffDist_optimal, ghDist, ghDist]
      _ = dist x y + dist y z := by rw [x.toGHSpace_rep, y.toGHSpace_rep, z.toGHSpace_rep]


end GHSpace --section

end GromovHausdorff

/-- In particular, nonempty compacts of a metric space map to `GHSpace`.
We register this in the `TopologicalSpace` namespace to take advantage
of the notation `p.toGHSpace`. -/
/-
**TopologicalSpace.NonemptyCompacts.toGHSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X] (
p : NonemptyCompacts X) : GromovHausdorff.GHSpace
参数：p : NonemptyCompacts X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In particular, nonempty compacts of a metric space map to `GHSpace`.
We register this in the `TopologicalSpace` namespace to take advantage
of the notation `p.toGHSpace`.
-/
def TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X]
    (p : NonemptyCompacts X) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace p

namespace GromovHausdorff

section NonemptyCompacts

variable {X : Type u} [MetricSpace X]

/-
**GromovHausdorff.ghDist_le_nonemptyCompacts_dist** 是 Mathlib 中的一个定理，位于命名空间 `Gro
movHausdorff`。
形式化陈述：ghDist_le_nonemptyCompacts_dist (p q : NonemptyCompacts X) : dist p.toGHSp
ace q.toGHSpace <= dist p q
参数：p q : NonemptyCompacts X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GromovHausdorff.ghDist_le_hausdorffDist`：ghDist_le_hausdorffDist {X : Ty
pe u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y]
 [CompactSpace Y] [Nonempty Y…
-/
theorem ghDist_le_nonemptyCompacts_dist (p q : NonemptyCompacts X) :
    dist p.toGHSpace q.toGHSpace ≤ dist p q := by
  have ha : Isometry ((↑) : p → X) := isometry_subtype_coe
  have hb : Isometry ((↑) : q → X) := isometry_subtype_coe
  have A : dist p q = hausdorffDist (p : Set X) q := rfl
  have I : ↑p = range ((↑) : p → X) := Subtype.range_coe_subtype.symm
  have J : ↑q = range ((↑) : q → X) := Subtype.range_coe_subtype.symm
  rw [A, I, J]
  exact ghDist_le_hausdorffDist ha hb
/-
**GromovHausdorff.toGHSpace_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdorff
`。
形式化陈述：toGHSpace_lipschitz : LipschitzWith 1 (NonemptyCompacts.toGHSpace : Nonemp
tyCompacts X -> GHSpace)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.mk_one`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSp
ace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f
 y) ≤ dist…
· 使用定理 `GromovHausdorff.ghDist_le_nonemptyCompacts_dist`：ghDist_le_nonemptyCompa
cts_dist (p q : NonemptyCompacts X) : dist p.toGHSpace q.toGHSpace <= dist p q
-/
theorem toGHSpace_lipschitz :
    LipschitzWith 1 (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  LipschitzWith.mk_one ghDist_le_nonemptyCompacts_dist
/-
**GromovHausdorff.toGHSpace_continuous** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdorf
f`。
形式化陈述：toGHSpace_continuous : Continuous (NonemptyCompacts.toGHSpace : NonemptyCo
mpacts X -> GHSpace)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `GromovHausdorff.toGHSpace_lipschitz`：toGHSpace_lipschitz : LipschitzWith
 1 (NonemptyCompacts.toGHSpace : NonemptyCompacts X -> GHSpace)
-/
theorem toGHSpace_continuous :
    Continuous (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  toGHSpace_lipschitz.continuous

end NonemptyCompacts

section

/- In this section, we show that if two metric spaces are isometric up to `ε₂`, then their
Gromov-Hausdorff distance is bounded by `ε₂ / 2`. More generally, if there are subsets which are
`ε₁`-dense and `ε₃`-dense in two spaces, and isometric up to `ε₂`, then the Gromov-Hausdorff
distance between the spaces is bounded by `ε₁ + ε₂/2 + ε₃`. For this, we construct a suitable
coupling between the two spaces, by gluing them (approximately) along the two matching subsets. -/
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]

/-- If there are subsets which are `ε₁`-dense and `ε₃`-dense in two spaces, and
isometric up to `ε₂`, then the Gromov-Hausdorff distance between the spaces is bounded by
`ε₁ + ε₂/2 + ε₃`. -/
/-
**GromovHausdorff.ghDist_le_of_approx_subsets** 是 Mathlib 中的一个定理，位于命名空间 `GromovH
ausdorff`。
形式化陈述：ghDist_le_of_approx_subsets {s : Set X} (Φ : s -> Y) {ε₁ ε₂ ε₃ : Real} (hs
 : forall x : X, exists y in s, dist x y <= ε₁) (hs' : forall x : Y, exists y : 
s, dist x (Φ y) <= ε₃) (H : forall x y : s, |dist x y - dist (Φ x) (Φ y)| <= ε₂)
 : ghDist X Y <= ε₁ + ε₂ / 2 + ε₃
参数：Φ : s -> Y；hs : forall x : X, exists y in s, dist x y <= ε₁；hs' : forall x : 
Y, exists y : s, dist x (Φ y) <= ε₃；H : forall x y : s, |dist x y - dist (Φ x) (
Φ y)| <= ε₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.exists_mem_of_nonempty`：∀ (α : Type u_1) [Nonempty α], ∃ x, x ∈ Set.
univ
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 104 条，此处仅展示前 30 条）

--- 原说明 ---
If there are subsets which are `ε₁`-dense and `ε₃`-dense in two spaces, and
isometric up to `ε₂`, then the Gromov-Hausdorff distance between the spaces is b
ounded by
`ε₁ + ε₂/2 + ε₃`.
-/
theorem ghDist_le_of_approx_subsets {s : Set X} (Φ : s → Y) {ε₁ ε₂ ε₃ : ℝ}
    (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁) (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃)
    (H : ∀ x y : s, |dist x y - dist (Φ x) (Φ y)| ≤ ε₂) : ghDist X Y ≤ ε₁ + ε₂ / 2 + ε₃ := by
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  rcases hs xX with ⟨xs, hxs, Dxs⟩
  have sne : s.Nonempty := ⟨xs, hxs⟩
  let _ : Nonempty s := sne.to_subtype
  have : 0 ≤ ε₂ := le_trans (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩)
  have : ∀ p q : s, |dist p q - dist (Φ p) (Φ q)| ≤ 2 * (ε₂ / 2 + δ) := fun p q =>
    calc
      |dist p q - dist (Φ p) (Φ q)| ≤ ε₂ := H p q
      _ ≤ 2 * (ε₂ / 2 + δ) := by linarith
  -- glue `X` and `Y` along the almost matching subsets
  let _ : MetricSpace (X ⊕ Y) :=
    glueMetricApprox (fun x : s => (x : X)) (fun x => Φ x) (ε₂ / 2 + δ) (by linarith) this
  let Fl := @Sum.inl X Y
  let Fr := @Sum.inr X Y
  have Il : Isometry Fl := Isometry.of_dist_eq fun x y => rfl
  have Ir : Isometry Fr := Isometry.of_dist_eq fun x y => rfl
  /- The proof goes as follows : the `ghDist` is bounded by the Hausdorff distance of the images
    in the coupling, which is bounded (using the triangular inequality) by the sum of the Hausdorff
    distances of `X` and `s` (in the coupling or, equivalently in the original space), of `s` and
    `Φ s`, and of `Φ s` and `Y` (in the coupling or, equivalently, in the original space).
    The first term is bounded by `ε₁`, by `ε₁`-density. The third one is bounded by `ε₃`.
    And the middle one is bounded by `ε₂/2` as in the coupling the points `x` and `Φ x` are
    at distance `ε₂/2` by construction of the coupling (in fact `ε₂/2 + δ` where `δ` is an
    arbitrarily small positive constant where positivity is used to ensure that the coupling
    is really a metric space and not a premetric space on `X ⊕ Y`). -/
  have : ghDist X Y ≤ hausdorffDist (range Fl) (range Fr) := ghDist_le_hausdorffDist Il Ir
  have :
    hausdorffDist (range Fl) (range Fr) ≤
      hausdorffDist (range Fl) (Fl '' s) + hausdorffDist (Fl '' s) (range Fr) :=
    have B : IsBounded (range Fl) := (isCompact_range Il.continuous).isBounded
    hausdorffDist_triangle
      (hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (sne.image _) B
        (B.subset (image_subset_range _ _)))
  have :
    hausdorffDist (Fl '' s) (range Fr) ≤
      hausdorffDist (Fl '' s) (Fr '' range Φ) + hausdorffDist (Fr '' range Φ) (range Fr) :=
    have B : IsBounded (range Fr) := (isCompact_range Ir.continuous).isBounded
    hausdorffDist_triangle'
      (hausdorffEDist_ne_top_of_nonempty_of_bounded ((range_nonempty _).image _) (range_nonempty _)
        (B.subset (image_subset_range _ _)) B)
  have : hausdorffDist (range Fl) (Fl '' s) ≤ ε₁ := by
    rw [← image_univ, hausdorffDist_image Il]
    have : 0 ≤ ε₁ := le_trans dist_nonneg Dxs
    refine hausdorffDist_le_of_mem_dist this (fun x _ => hs x) fun x _ =>
      ⟨x, mem_univ _, by simpa only [dist_self]⟩
  have : hausdorffDist (Fl '' s) (Fr '' range Φ) ≤ ε₂ / 2 + δ := by
    refine hausdorffDist_le_of_mem_dist (by linarith) ?_ ?_
    · intro x' hx'
      rcases (Set.mem_image _ _ _).1 hx' with ⟨x, ⟨x_in_s, xx'⟩⟩
      rw [← xx']
      use Fr (Φ ⟨x, x_in_s⟩), mem_image_of_mem Fr (mem_range_self _)
      exact le_of_eq (glueDist_glued_points (fun x : s => (x : X)) Φ (ε₂ / 2 + δ) ⟨x, x_in_s⟩)
    · intro x' hx'
      rcases (Set.mem_image _ _ _).1 hx' with ⟨y, ⟨y_in_s', yx'⟩⟩
      rcases mem_range.1 y_in_s' with ⟨x, xy⟩
      use Fl x, mem_image_of_mem _ x.2
      rw [← yx', ← xy, dist_comm]
      exact le_of_eq (glueDist_glued_points (Z := s) Subtype.val Φ (ε₂ / 2 + δ) x)
  have : hausdorffDist (Fr '' range Φ) (range Fr) ≤ ε₃ := by
    rw [← @image_univ _ _ Fr, hausdorffDist_image Ir]
    rcases exists_mem_of_nonempty Y with ⟨xY, _⟩
    rcases hs' xY with ⟨xs', Dxs'⟩
    have : 0 ≤ ε₃ := le_trans dist_nonneg Dxs'
    refine hausdorffDist_le_of_mem_dist this
      (fun x _ => ⟨x, mem_univ _, by simpa only [dist_self]⟩)
      fun x _ => ?_
    rcases hs' x with ⟨y, Dy⟩
    exact ⟨Φ y, mem_range_self _, Dy⟩
  linarith

end --section

set_option backward.isDefEq.respectTransparency false in
/-- The Gromov-Hausdorff space is second countable. -/
/-
**GromovHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gromov-Hausdorff space is second countable.
-/
instance : SecondCountableTopology GHSpace := by
  refine secondCountable_of_countable_discretization fun δ δpos => ?_
  let ε := 2 / 5 * δ
  have εpos : 0 < ε := mul_pos (by simp) δpos
  have (p : GHSpace) : ∃ s : Set p.Rep, s.Finite ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
    simpa only [subset_univ, true_and] using
      finite_cover_balls_of_compact (X := p.Rep) isCompact_univ εpos
  -- for each `p`, `s p` is a finite `ε`-dense subset of `p` (or rather the metric space
  -- `p.Rep` representing `p`)
  choose s hs using this
  -- cardinality of the nice finite subset `s p` of `p.Rep`, called `N p`
  let N := fun p : GHSpace => Nat.card (s p)
  -- equiv from `s p`, a nice finite subset of `p.Rep`, to `Fin (N p)`, called `E p`
  let E := fun p : GHSpace => (hs p).1.equivFin
  -- A function `F` associating to `p : GHSpace` the data of all distances between points
  -- in the `ε`-dense set `s p`.
  let F : GHSpace → Σ n : ℕ, Fin n → Fin n → ℤ := fun p =>
    ⟨N p, fun a b => ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋⟩
  refine ⟨Σ n, Fin n → Fin n → ℤ, inferInstance, F, fun p q hpq => ?_⟩
  /- As the target space of F is countable, it suffices to show that two points
  `p` and `q` with `F p = F q` are at distance `≤ δ`.
  For this, we construct a map `Φ` from `s p ⊆ p.Rep` (representing `p`)
  to `q.Rep` (representing `q`) which is almost an isometry on `s p`, and
  with image `s q`. For this, we compose the identification of `s p` with `Fin (N p)`
  and the inverse of the identification of `s q` with `Fin (N q)`. Together with
  the fact that `N p = N q`, this constructs `Ψ` between `s p` and `s q`, and then
  composing with the canonical inclusion we get `Φ`. -/
  have Npq : N p = N q := (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Fin.cast Npq ((E p) x))
  let Φ : s p → q.Rep := fun x => Ψ x
  -- Use the almost isometry `Φ` to show that `p.Rep` and `q.Rep`
  -- are within controlled Gromov-Hausdorff distance.
  have main : ghDist p.Rep q.Rep ≤ ε + ε / 2 + ε := by
    refine ghDist_le_of_approx_subsets Φ ?_ ?_ ?_
    · show ∀ x : p.Rep, ∃ y ∈ s p, dist x y ≤ ε
      -- by construction, `s p` is `ε`-dense
      intro x
      have : x ∈ ⋃ y ∈ s p, ball y ε := (hs p).2 (mem_univ _)
      obtain ⟨y, ys, hy⟩ := mem_iUnion₂.1 this
      exact ⟨y, ys, hy.le⟩
    · show ∀ x : q.Rep, ∃ z : s p, dist x (Φ z) ≤ ε
      -- by construction, `s q` is `ε`-dense, and it is the range of `Φ`
      intro x
      have : x ∈ ⋃ y ∈ s q, ball y ε := (hs q).2 (mem_univ _)
      obtain ⟨y, ys, hy⟩ := mem_iUnion₂.1 this
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).is_lt
      have ihi_eq : (⟨i, hi⟩ : Fin (N q)) = (E q) ⟨y, ys⟩ := by rw [Fin.ext_iff, Fin.val_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ := by
        rw [ihi_eq]; exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by simp only [Φ, Ψ]; rw [C1, C2, C3]
      rw [this]
      exact hy.le
    · show ∀ x y : s p, |dist x y - dist (Φ x) (Φ y)| ≤ ε
      /- the distance between `x` and `y` is encoded in `F p`, and the distance between
      `Φ x` and `Φ y` (two points of `s q`) is encoded in `F q`, all this up to `ε`.
      As `F p = F q`, the distances are almost equal. -/
      intro x y
      -- introduce `i`, that codes both `x` and `Φ x` in `Fin (N p) = Fin (N q)`
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by simp only [i, Ψ, Equiv.apply_symm_apply, Fin.val_cast]
      -- introduce `j`, that codes both `y` and `Φ y` in `Fin (N p) = Fin (N q)`
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by rwa [Npq] at hjp
      have j' : j = ((E q) (Ψ y)).1 := by
        simp only [j, Ψ, Equiv.apply_symm_apply, Fin.val_cast]
      -- Express `dist x y` in terms of `F p`
      have : (F p).2 ((E p) x) ((E p) y) = ⌊ε⁻¹ * dist x y⌋ := by
        simp only [F, (E p).symm_apply_apply]
      have Ap : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = ⌊ε⁻¹ * dist x y⌋ := by rw [← this]
      -- Express `dist (Φ x) (Φ y)` in terms of `F q`
      have : (F q).2 ((E q) (Ψ x)) ((E q) (Ψ y)) = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        simp only [F, (E q).symm_apply_apply]
      have Aq : (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        simp [← this, *]
      -- use the equality between `F p` and `F q` to deduce that the distances have equal
      -- integer parts
      have : (F p).2 ⟨i, hip⟩ ⟨j, hjp⟩ = (F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩ := by
        have hpq' : (F p).snd ≍ (F q).snd := (Sigma.mk.inj_iff.1 hpq).2
        rw [Fin.heq_fun₂_iff Npq Npq] at hpq'
        rw [← hpq']
      rw [Ap, Aq] at this
      -- deduce that the distances coincide up to `ε`, by a straightforward computation
      -- that should be automated
      have I :=
        calc
          ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)| = |ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))| := by
            rw [abs_mul, abs_of_nonneg (inv_pos.2 εpos).le]
          _ = |ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)| := by congr; ring
          _ ≤ 1 := le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)
      calc
        |dist x y - dist (Ψ x) (Ψ y)|
        _ = ε * (ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)|) := by
            #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
            (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed
            this goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a
            problem in the new canonicalizer; a minimization would help. The original proof was:
            `grind` -/
            field_simp
        _ ≤ ε * 1 := by gcongr
        _ = ε := mul_one _
  calc
    dist p q = ghDist p.Rep q.Rep := dist_ghDist p q
    _ ≤ ε + ε / 2 + ε := main
    _ = δ := by ring

/-- Compactness criterion: a closed set of compact metric spaces is compact if the spaces have
a uniformly bounded diameter, and for all `ε` the number of balls of radius `ε` required
to cover the spaces is uniformly bounded. This is an equivalence, but we only prove the
interesting direction that these conditions imply compactness. -/
/-
**GromovHausdorff.totallyBounded** 是 Mathlib 中的一个定理，位于命名空间 `GromovHausdorff`。
形式化陈述：totallyBounded {t : Set GHSpace} {C : Real} {u : Nat -> Real} {K : Nat -> 
Nat} (ulim : Tendsto u atTop (𝓝 0)) (hdiam : forall p in t, diam (univ : Set (GH
Space.Rep p)) <= C) (hcov : forall p in t, forall n : Nat, exists s : Set (GHSpa
ce.Rep p), (#s) <= K n ∧ univ subseteq ⋃ x in s, ball x (u n)) : TotallyBounded 
t
参数：ulim : Tendsto u atTop (𝓝 0)；hdiam : forall p in t, diam (univ : Set (GHSpace
.Rep p)) <= C；hcov : forall p in t, forall n : Nat, exists s : Set (GHSpace.Rep 
p), (#s) <= K n ∧ univ subseteq ⋃ x in s, ball x (u n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.totallyBounded_of_finite_discretization`：totallyBounded_of_finite
_discretization {s : Set α} (H : forall ε > (0 : Real), exists (β : Type u) (_ :
 Fintype β) (F : s -> β), forall x y…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Set.card_empty`：card_empty : Fintype.card (∅ : Set α) = 0
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Set.not_notMem`：not_notMem : ¬a ∉ s ↔ a in s
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
（共 132 条，此处仅展示前 30 条）

--- 原说明 ---
Compactness criterion: a closed set of compact metric spaces is compact if the s
paces have
a uniformly bounded diameter, and for all `ε` the number of balls of radius `ε` 
required
to cover the spaces is uniformly bounded. This is an equivalence, but we only pr
ove the
interesting direction that these conditions imply compactness.
-/
theorem totallyBounded {t : Set GHSpace} {C : ℝ} {u : ℕ → ℝ} {K : ℕ → ℕ}
    (ulim : Tendsto u atTop (𝓝 0)) (hdiam : ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C)
    (hcov : ∀ p ∈ t, ∀ n : ℕ, ∃ s : Set (GHSpace.Rep p),
      (#s) ≤ K n ∧ univ ⊆ ⋃ x ∈ s, ball x (u n)) :
    TotallyBounded t := by
  /- Let `δ>0`, and `ε = δ/5`. For each `p`, we construct a finite subset `s p` of `p`, which
    is `ε`-dense and has cardinality at most `K n`. Encoding the mutual distances of points
    in `s p`, up to `ε`, we will get a map `F` associating to `p` finitely many data, and making
    it possible to reconstruct `p` up to `ε`. This is enough to prove total boundedness. -/
  refine Metric.totallyBounded_of_finite_discretization fun δ δpos => ?_
  let ε := 1 / 5 * δ
  have εpos : 0 < ε := mul_pos (by simp) δpos
  -- choose `n` for which `u n < ε`
  rcases Metric.tendsto_atTop.1 ulim ε εpos with ⟨n, hn⟩
  have u_le_ε : u n ≤ ε := by
    have := hn n le_rfl
    simp only [Real.dist_eq, add_zero, sub_eq_add_neg, neg_zero] at this
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) this)
  -- construct a finite subset `s p` of `p` which is `ε`-dense and has cardinal `≤ K n`
  have :
    ∀ p : GHSpace,
      ∃ s : Set p.Rep, ∃ N ≤ K n, ∃ _ : Equiv s (Fin N), p ∈ t → univ ⊆ ⋃ x ∈ s, ball x (u n) := by
    intro p
    by_cases hp : p ∉ t
    · have : Nonempty (Equiv (∅ : Set p.Rep) (Fin 0)) := by
        rw [← Fintype.card_eq, card_empty, Fintype.card_fin]
      use ∅, 0, bot_le, this.some
      exact fun hp' => (hp hp').elim
    · rcases hcov _ (Set.not_notMem.1 hp) n with ⟨s, ⟨scard, scover⟩⟩
      rcases Cardinal.lt_aleph0.1 (scard.trans_lt Cardinal.natCast_lt_aleph0) with ⟨N, hN⟩
      rw [hN, Nat.cast_le] at scard
      have : #s = #(Fin N) := by rw [hN, Cardinal.mk_fin]
      obtain ⟨E⟩ := Quotient.exact this
      use s, N, scard, E
      simp only [scover, imp_true_iff]
  choose s N hN E hs using this
  -- Define a function `F` taking values in a finite type and associating to `p` enough data
  -- to reconstruct it up to `ε`, namely the (discretized) distances between elements of `s p`.
  let M := ⌊ε⁻¹ * max C 0⌋₊
  let F : GHSpace → Σ k : Fin (K n).succ, Fin k → Fin k → Fin M.succ := fun p =>
    ⟨⟨N p, lt_of_le_of_lt (hN p) (Nat.lt_succ_self _)⟩, fun a b =>
      ⟨min M ⌊ε⁻¹ * dist ((E p).symm a) ((E p).symm b)⌋₊,
        (min_le_left _ _).trans_lt (Nat.lt_succ_self _)⟩⟩
  refine ⟨_, ?_, fun p => F p, ?_⟩
  · infer_instance
  -- It remains to show that if `F p = F q`, then `p` and `q` are `ε`-close
  rintro ⟨p, pt⟩ ⟨q, qt⟩ hpq
  have Npq : N p = N q := Fin.ext_iff.1 (Sigma.mk.inj_iff.1 hpq).1
  let Ψ : s p → s q := fun x => (E q).symm (Fin.cast Npq ((E p) x))
  let Φ : s p → q.Rep := fun x => Ψ x
  have main : ghDist p.Rep q.Rep ≤ ε + ε / 2 + ε := by
    -- to prove the main inequality, argue that `s p` is `ε`-dense in `p`, and `s q` is `ε`-dense
    -- in `q`, and `s p` and `s q` are almost isometric. Then closeness follows
    -- from `ghDist_le_of_approx_subsets`
    refine ghDist_le_of_approx_subsets Φ ?_ ?_ ?_
    · show ∀ x : p.Rep, ∃ y ∈ s p, dist x y ≤ ε
      -- by construction, `s p` is `ε`-dense
      intro x
      have : x ∈ ⋃ y ∈ s p, ball y (u n) := (hs p pt) (mem_univ _)
      rcases mem_iUnion₂.1 this with ⟨y, ys, hy⟩
      exact ⟨y, ys, le_trans (le_of_lt hy) u_le_ε⟩
    · show ∀ x : q.Rep, ∃ z : s p, dist x (Φ z) ≤ ε
      -- by construction, `s q` is `ε`-dense, and it is the range of `Φ`
      intro x
      have : x ∈ ⋃ y ∈ s q, ball y (u n) := (hs q qt) (mem_univ _)
      rcases mem_iUnion₂.1 this with ⟨y, ys, hy⟩
      let i : ℕ := E q ⟨y, ys⟩
      let hi := ((E q) ⟨y, ys⟩).2
      have ihi_eq : (⟨i, hi⟩ : Fin (N q)) = (E q) ⟨y, ys⟩ := by rw [Fin.ext_iff, Fin.val_mk]
      have hiq : i < N q := hi
      have hip : i < N p := by rwa [Npq.symm] at hiq
      let z := (E p).symm ⟨i, hip⟩
      use z
      have C1 : (E p) z = ⟨i, hip⟩ := (E p).apply_symm_apply ⟨i, hip⟩
      have C2 : Fin.cast Npq ⟨i, hip⟩ = ⟨i, hi⟩ := rfl
      have C3 : (E q).symm ⟨i, hi⟩ = ⟨y, ys⟩ := by
        rw [ihi_eq]; exact (E q).symm_apply_apply ⟨y, ys⟩
      have : Φ z = y := by simp only [Ψ, Φ]; rw [C1, C2, C3]
      rw [this]
      exact le_trans (le_of_lt hy) u_le_ε
    · show ∀ x y : s p, |dist x y - dist (Φ x) (Φ y)| ≤ ε
      /- the distance between `x` and `y` is encoded in `F p`, and the distance between
            `Φ x` and `Φ y` (two points of `s q`) is encoded in `F q`, all this up to `ε`.
            As `F p = F q`, the distances are almost equal. -/
      intro x y
      have : dist (Φ x) (Φ y) = dist (Ψ x) (Ψ y) := rfl
      rw [this]
      -- introduce `i`, that codes both `x` and `Φ x` in `Fin (N p) = Fin (N q)`
      let i : ℕ := E p x
      have hip : i < N p := ((E p) x).2
      have hiq : i < N q := by rwa [Npq] at hip
      have i' : i = (E q) (Ψ x) := by simp only [i, Ψ, Equiv.apply_symm_apply, Fin.val_cast]
      -- introduce `j`, that codes both `y` and `Φ y` in `Fin (N p) = Fin (N q)`
      let j : ℕ := E p y
      have hjp : j < N p := ((E p) y).2
      have hjq : j < N q := by rwa [Npq] at hjp
      have j' : j = (E q) (Ψ y) := by simp only [j, Ψ, Equiv.apply_symm_apply, Fin.val_cast]
      -- Express `dist x y` in terms of `F p`
      have Ap : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ⌊ε⁻¹ * dist x y⌋₊ :=
        calc
          ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F p).2 ((E p) x) ((E p) y)).1 := by
            congr
          _ = min M ⌊ε⁻¹ * dist x y⌋₊ := by simp only [F, (E p).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist x y⌋₊ := by
            refine min_eq_right (Nat.floor_mono ?_)
            refine mul_le_mul_of_nonneg_left (le_trans ?_ (le_max_left _ _)) (inv_pos.2 εpos).le
            change dist (x : p.Rep) y ≤ C
            refine (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans ?_
            exact hdiam p pt
      -- Express `dist (Φ x) (Φ y)` in terms of `F q`
      have Aq : ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ :=
        calc
          ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 = ((F q).2 ((E q) (Ψ x)) ((E q) (Ψ y))).1 := by
            congr!
          _ = min M ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by simp only [F, (E q).symm_apply_apply]
          _ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋₊ := by
            refine min_eq_right (Nat.floor_mono ?_)
            refine mul_le_mul_of_nonneg_left (le_trans ?_ (le_max_left _ _)) (inv_pos.2 εpos).le
            change dist (Ψ x : q.Rep) (Ψ y) ≤ C
            refine (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans ?_
            exact hdiam q qt
      -- use the equality between `F p` and `F q` to deduce that the distances have equal
      -- integer parts
      have : ((F p).2 ⟨i, hip⟩ ⟨j, hjp⟩).1 = ((F q).2 ⟨i, hiq⟩ ⟨j, hjq⟩).1 := by
        have hpq' : (F p).snd ≍ (F q).snd := (Sigma.mk.inj_iff.1 hpq).2
        rw [Fin.heq_fun₂_iff Npq Npq] at hpq'
        rw [← hpq']
      have : ⌊ε⁻¹ * dist x y⌋ = ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ := by
        rw [Ap, Aq] at this
        have D : 0 ≤ ⌊ε⁻¹ * dist x y⌋ :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)
        have D' : 0 ≤ ⌊ε⁻¹ * dist (Ψ x) (Ψ y)⌋ :=
          floor_nonneg.2 (mul_nonneg (le_of_lt (inv_pos.2 εpos)) dist_nonneg)
        rw [← Int.toNat_of_nonneg D, ← Int.toNat_of_nonneg D', Int.floor_toNat, Int.floor_toNat,
          this]
      -- deduce that the distances coincide up to `ε`, by a straightforward computation
      -- that should be automated
      have I :=
        calc
          |ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)| = |ε⁻¹ * (dist x y - dist (Ψ x) (Ψ y))| :=
            (abs_mul _ _).symm
          _ = |ε⁻¹ * dist x y - ε⁻¹ * dist (Ψ x) (Ψ y)| := by congr; ring
          _ ≤ 1 := le_of_lt (abs_sub_lt_one_of_floor_eq_floor this)
      calc
        |dist x y - dist (Ψ x) (Ψ y)| = ε * ε⁻¹ * |dist x y - dist (Ψ x) (Ψ y)| := by
          rw [mul_inv_cancel₀ (ne_of_gt εpos), one_mul]
        _ = ε * (|ε⁻¹| * |dist x y - dist (Ψ x) (Ψ y)|) := by
          rw [abs_of_nonneg (le_of_lt (inv_pos.2 εpos)), mul_assoc]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left I (le_of_lt εpos)
        _ = ε := mul_one _
  calc
    dist p q = ghDist p.Rep q.Rep := dist_ghDist p q
    _ ≤ ε + ε / 2 + ε := main
    _ = δ / 2 := by simp only [ε, one_div]; ring
    _ < δ := half_lt_self δpos

section Complete

/- We will show that a sequence `u n` of compact metric spaces satisfying
`dist (u n) (u (n+1)) < 1/2^n` converges, which implies completeness of the Gromov-Hausdorff space.
We need to exhibit the limiting compact metric space. For this, start from
a sequence `X n` of representatives of `u n`, and glue in an optimal way `X n` to `X (n+1)`
for all `n`, in a common metric space. Formally, this is done as follows.
Start from `Y 0 = X 0`. Then, glue `X 0` to `X 1` in an optimal way, yielding a space
`Y 1` (with an embedding of `X 1`). Then, consider an optimal gluing of `X 1` and `X 2`, and
glue it to `Y 1` along their common subspace `X 1`. This gives a new space `Y 2`, with an
embedding of `X 2`. Go on, to obtain a sequence of spaces `Y n`. Let `Z0` be the inductive
limit of the `Y n`, and finally let `Z` be the completion of `Z0`.
The images `X2 n` of `X n` in `Z` are at Hausdorff distance `< 1/2^n` by construction, hence they
form a Cauchy sequence for the Hausdorff distance. By completeness (of `Z`, and therefore of its
set of nonempty compact subsets), they converge to a limit `L`. This is the nonempty
compact metric space we are looking for. -/
variable (X : ℕ → Type) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]

/-- Auxiliary structure used to glue metric spaces below, recording an isometric embedding
of a type `A` in another metric space. -/
/-
**GromovHausdorff.AuxGluingStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `GromovHausdorff`。
形式化陈述：(A : Type) → [MetricSpace A] → Type 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary structure used to glue metric spaces below, recording an isometric emb
edding
of a type `A` in another metric space.
-/
structure AuxGluingStruct (A : Type) [MetricSpace A] : Type 1 where
  Space : Type
  metric : MetricSpace Space
  embed : A → Space
  isom : Isometry embed

attribute [local instance] AuxGluingStruct.metric
/-
**GromovHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Type) [MetricSpace A] : Inhabited (AuxGluingStruct A) :=
  ⟨{  Space := A
      metric := by infer_instance
      embed := id
      isom _ _ := rfl }⟩

/-- Auxiliary sequence of metric spaces, containing copies of `X 0`, ..., `X n`, where each
`X i` is glued to `X (i+1)` in an optimal way. The space at step `n+1` is obtained from the space
at step `n` by adding `X (n+1)`, glued in an optimal way to the `X n` already sitting there. -/
/-
**GromovHausdorff.auxGluing** 是 Mathlib 中的一个定义，位于命名空间 `GromovHausdorff`。
形式化陈述：auxGluing (n : Nat) : AuxGluingStruct (X n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary sequence of metric spaces, containing copies of `X 0`, ..., `X n`, whe
re each
`X i` is glued to `X (i+1)` in an optimal way. The space at step `n+1` is obtain
ed from the space
at step `n` by adding `X (n+1)`, glued in an optimal way to the `X n` already si
tting there.
-/
def auxGluing (n : ℕ) : AuxGluingStruct (X n) :=
  Nat.recOn n default fun n Y =>
    { Space := GlueSpace Y.isom (isometry_optimalGHInjl (X n) (X (n + 1)))
      metric := by infer_instance
      embed :=
        toGlueR Y.isom (isometry_optimalGHInjl (X n) (X (n + 1))) ∘ optimalGHInjr (X n) (X (n + 1))
      isom := (toGlueR_isometry _ _).comp (isometry_optimalGHInjr (X n) (X (n + 1))) }

set_option backward.isDefEq.respectTransparency false in
/-- The Gromov-Hausdorff space is complete. -/
/-
**GromovHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `GromovHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gromov-Hausdorff space is complete.
-/
instance : CompleteSpace GHSpace := by
  set d := fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n
  have : ∀ n : ℕ, 0 < d n := fun _ ↦ by positivity
  -- start from a sequence of nonempty compact metric spaces within distance `1/2^n` of each other
  refine Metric.complete_of_convergent_controlled_sequences d this fun u hu => ?_
  -- `X n` is a representative of `u n`
  let X n := (u n).Rep
  -- glue them together successively in an optimal way, getting a sequence of metric spaces `Y n`
  let Y := auxGluing X
  -- this equality is true by definition but Lean unfolds some defs in the wrong order
  have E :
    ∀ n : ℕ,
      GlueSpace (Y n).isom (isometry_optimalGHInjl (X n) (X (n + 1))) = (Y (n + 1)).Space :=
    fun n => by dsimp only [Y, auxGluing]
  let c n := cast (E n)
  have ic : ∀ n, Isometry (c n) := fun n x y => by dsimp only [Y, auxGluing]; exact rfl
  -- there is a canonical embedding of `Y n` in `Y (n+1)`, by construction
  let f : ∀ n, (Y n).Space → (Y (n + 1)).Space := fun n =>
    c n ∘ toGlueL (Y n).isom (isometry_optimalGHInjl (X n) (X n.succ))
  have I : ∀ n, Isometry (f n) := fun n => (ic n).comp (toGlueL_isometry _ _)
  -- consider the inductive limit `Z0` of the `Y n`, and then its completion `Z`
  let Z0 := Metric.InductiveLimit I
  let Z := UniformSpace.Completion Z0
  let Φ := toInductiveLimit I
  let coeZ := ((↑) : Z0 → Z)
  -- let `X2 n` be the image of `X n` in the space `Z`
  let X2 n := range (coeZ ∘ Φ n ∘ (Y n).embed)
  have isom : ∀ n, Isometry (coeZ ∘ Φ n ∘ (Y n).embed) := by
    intro n
    refine UniformSpace.Completion.coe_isometry.comp ?_
    exact (toInductiveLimit_isometry _ _).comp (Y n).isom
  -- The Hausdorff distance of `X2 n` and `X2 (n+1)` is by construction the distance between
  -- `u n` and `u (n+1)`, therefore bounded by `1/2^n`
  have X2n : ∀ n, X2 n =
    range ((coeZ ∘ Φ n.succ ∘ c n ∘ toGlueR (Y n).isom
      (isometry_optimalGHInjl (X n) (X n.succ))) ∘ optimalGHInjl (X n) (X n.succ)) := by
    intro n
    change X2 n = range (coeZ ∘ Φ n.succ ∘ c n ∘
      toGlueR (Y n).isom (isometry_optimalGHInjl (X n) (X n.succ)) ∘
      optimalGHInjl (X n) (X n.succ))
    simp only [X2, Φ]
    rw [← toInductiveLimit_commute I]
    simp only [f, ← toGlue_commute, Function.comp_assoc]
  have X2nsucc : ∀ n, X2 n.succ =
      range ((coeZ ∘ Φ n.succ ∘ c n ∘ toGlueR (Y n).isom
        (isometry_optimalGHInjl (X n) (X n.succ))) ∘ optimalGHInjr (X n) (X n.succ)) := by
    intro n
    rfl
  have D2 : ∀ n, hausdorffDist (X2 n) (X2 n.succ) < d n := fun n ↦ by
    rw [X2n n, X2nsucc n, range_comp, range_comp, hausdorffDist_image,
      hausdorffDist_optimal, ← dist_ghDist]
    · exact hu n n n.succ (le_refl n) (le_succ n)
    · apply UniformSpace.Completion.coe_isometry.comp _
      exact (toInductiveLimit_isometry _ _).comp ((ic n).comp (toGlueR_isometry _ _))
  -- consider `X2 n` as a member `X3 n` of the type of nonempty compact subsets of `Z`, which
  -- is a metric space
  let X3 : ℕ → NonemptyCompacts Z := fun n =>
    ⟨⟨X2 n, isCompact_range (isom n).continuous⟩, range_nonempty _⟩
  -- `X3 n` is a Cauchy sequence by construction, as the successive distances are
  -- bounded by `(1/2)^n`
  have : CauchySeq X3 := by
    refine cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num) fun n => ?_
    rw [one_mul]
    exact le_of_lt (D2 n)
  -- therefore, it converges to a limit `L`
  rcases cauchySeq_tendsto_of_complete this with ⟨L, hL⟩
  -- By construction, the image of `X3 n` in the Gromov-Hausdorff space is `u n`.
  have : ∀ n, (NonemptyCompacts.toGHSpace ∘ X3) n = u n := by
    intro n
    rw [Function.comp_apply, NonemptyCompacts.toGHSpace, ← (u n).toGHSpace_rep,
      toGHSpace_eq_toGHSpace_iff_isometryEquiv]
    constructor
    convert! (isom n).isometryEquivOnRange.symm
  -- the images of `X3 n` in the Gromov-Hausdorff space converge to the image of `L`
  -- so the images of `u n` converge to the image of `L` as well
  use L.toGHSpace
  apply Filter.Tendsto.congr this
  refine Tendsto.comp ?_ hL
  apply toGHSpace_continuous.tendsto

end Complete --section

end GromovHausdorff --namespace

