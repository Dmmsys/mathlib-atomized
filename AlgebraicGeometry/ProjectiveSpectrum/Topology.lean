/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Data.Set.Subsingleton

/-!
# Projective spectrum of a graded ring

The projective spectrum of a graded commutative ring is the subtype of all homogeneous ideals that
are prime and do not contain the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `A` is a commutative ring
- `σ` is a class of additive submonoids of `A`
- `𝒜 : ℕ → σ` is the grading of `A`;

## Main definitions

* `ProjectiveSpectrum 𝒜`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing irrelevant
  ideal. Henceforth, we call elements of projective spectrum *relevant homogeneous prime ideals*.
* `ProjectiveSpectrum.zeroLocus 𝒜 s`: The zero locus of a subset `s` of `A`
  is the subset of `ProjectiveSpectrum 𝒜` consisting of all relevant homogeneous prime ideals that
  contain `s`.
* `ProjectiveSpectrum.vanishingIdeal t`: The vanishing ideal of a subset `t` of
  `ProjectiveSpectrum 𝒜` is the intersection of points in `t` (viewed as relevant homogeneous prime
  ideals).
* `ProjectiveSpectrum.Top`: the topological space of `ProjectiveSpectrum 𝒜` endowed with the
  Zariski topology.
-/

@[expose] public section


noncomputable section

open DirectSum Pointwise SetLike TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective spectrum of a graded commutative ring is the subtype of all homogeneous ideals
that are prime and do not contain the irrelevant ideal. -/
@[ext]
/-
**ProjectiveSpectrum** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] → [inst_2 : AddSubmonoidClass σ A] → (𝒜 : ℕ → σ) → [GradedRing 
𝒜] → Type u_1
参数：𝒜 : ℕ → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projective spectrum of a graded commutative ring is the subtype of all homog
eneous ideals
that are prime and do not contain the irrelevant ideal.
-/
structure ProjectiveSpectrum where
  asHomogeneousIdeal : HomogeneousIdeal 𝒜
  isPrime : asHomogeneousIdeal.toIdeal.IsPrime
  not_irrelevant_le : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ asHomogeneousIdeal

attribute [instance] ProjectiveSpectrum.isPrime

namespace ProjectiveSpectrum

/-
**ProjectiveSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `ProjectiveSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : ProjectiveSpectrum 𝒜) : Ideal.IsPrime x.asHomogeneousIdeal.toIdeal := x.isPrime

/-- The zero locus of a set `s` of elements of a commutative ring `A` is the set of all relevant
homogeneous prime ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` takes values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `zeroLocus s` is exactly the subset
of `ProjectiveSpectrum 𝒜` where all "functions" in `s` vanish simultaneously. -/
/-
**ProjectiveSpectrum.zeroLocus** 是 Mathlib 中的一个定义，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：zeroLocus (s : Set A) : Set (ProjectiveSpectrum 𝒜)
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero locus of a set `s` of elements of a commutative ring `A` is the set of 
all relevant
homogeneous prime ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projectiv
e spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` take
s values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `zeroLocus s` is e
xactly the subset
of `ProjectiveSpectrum 𝒜` where all "functions" in `s` vanish simultaneously.
-/
def zeroLocus (s : Set A) : Set (ProjectiveSpectrum 𝒜) :=
  { x | s ⊆ x.asHomogeneousIdeal }

@[simp]
/-
**ProjectiveSpectrum.mem_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：mem_zeroLocus (x : ProjectiveSpectrum 𝒜) (s : Set A) : x in zeroLocus 𝒜 s 
↔ s subseteq x.asHomogeneousIdeal
参数：x : ProjectiveSpectrum 𝒜；s : Set A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_zeroLocus (x : ProjectiveSpectrum 𝒜) (s : Set A) :
    x ∈ zeroLocus 𝒜 s ↔ s ⊆ x.asHomogeneousIdeal :=
  Iff.rfl

@[simp]
/-
**ProjectiveSpectrum.zeroLocus_span** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectru
m`。
形式化陈述：zeroLocus_span (s : Set A) : zeroLocus 𝒜 (Ideal.span s) = zeroLocus 𝒜 s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem zeroLocus_span (s : Set A) : zeroLocus 𝒜 (Ideal.span s) = zeroLocus 𝒜 s := by
  ext x
  exact (Submodule.gi _ _).gc s x.asHomogeneousIdeal.toIdeal

variable {𝒜}

/-- The vanishing ideal of a set `t` of points of the projective spectrum of a commutative ring `R`
is the intersection of all the relevant homogeneous prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` takes values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `vanishingIdeal t` is exactly the
ideal of `A` consisting of all "functions" that vanish on all of `t`. -/
/-
**ProjectiveSpectrum.vanishingIdeal** 是 Mathlib 中的一个定义，位于命名空间 `ProjectiveSpectru
m`。
形式化陈述：vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : HomogeneousIdeal 𝒜
参数：t : Set (ProjectiveSpectrum 𝒜)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vanishing ideal of a set `t` of points of the projective spectrum of a commu
tative ring `R`
is the intersection of all the relevant homogeneous prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projectiv
e spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` take
s values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `vanishingIdeal t`
 is exactly the
ideal of `A` consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : HomogeneousIdeal 𝒜 :=
  ⨅ (x : ProjectiveSpectrum 𝒜) (_ : x ∈ t), x.asHomogeneousIdeal
/-
**ProjectiveSpectrum.coe_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpe
ctrum`。
形式化陈述：coe_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : (vanishingIdeal t : 
Set A) = { f | forall x : ProjectiveSpectrum 𝒜, x in t -> f in x.asHomogeneousId
eal }
参数：t : Set (ProjectiveSpectrum 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.vanishingIdeal.eq_1`：∀ {A : Type u_1} {σ : Type u_2} 
[inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 :
 ℕ → σ}   [inst_3 : GradedRi…
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousIdeal.mem_iff`：HomogeneousIdeal.mem_iff {I : HomogeneousIdeal
 𝒜} {x : A} : x in I.toIdeal ↔ x in I
· 使用定理 `HomogeneousIdeal.toIdeal_iInf`：toIdeal_iInf {κ : Sort*} (s : κ -> Homoge
neousIdeal 𝒜) : (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    (vanishingIdeal t : Set A) =
      { f | ∀ x : ProjectiveSpectrum 𝒜, x ∈ t → f ∈ x.asHomogeneousIdeal } := by
  ext f
  rw [vanishingIdeal, SetLike.mem_coe, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_iInf,
    Submodule.mem_iInf]
  refine forall_congr' fun x => ?_
  rw [HomogeneousIdeal.toIdeal_iInf, Submodule.mem_iInf, HomogeneousIdeal.mem_iff]
/-
**ProjectiveSpectrum.mem_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpe
ctrum`。
形式化陈述：mem_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (f : A) : f in vanishi
ngIdeal t ↔ forall x : ProjectiveSpectrum 𝒜, x in t -> f in x.asHomogeneousIdeal
参数：t : Set (ProjectiveSpectrum 𝒜)；f : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `ProjectiveSpectrum.coe_vanishingIdeal`：coe_vanishingIdeal (t : Set (Proj
ectiveSpectrum 𝒜)) : (vanishingIdeal t : Set A) = { f | forall x : ProjectiveSpe
ctrum 𝒜, x in t -> f in x.a…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (f : A) :
    f ∈ vanishingIdeal t ↔ ∀ x : ProjectiveSpectrum 𝒜, x ∈ t → f ∈ x.asHomogeneousIdeal := by
  rw [← SetLike.mem_coe, coe_vanishingIdeal, Set.mem_ofPred_eq]

@[simp]
/-
**ProjectiveSpectrum.vanishingIdeal_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Project
iveSpectrum`。
形式化陈述：vanishingIdeal_singleton (x : ProjectiveSpectrum 𝒜) : vanishingIdeal ({x} 
: Set (ProjectiveSpectrum 𝒜)) = x.asHomogeneousIdeal
参数：x : ProjectiveSpectrum 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_iInf_eq_left`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] {b : β} {f : (x : β) → x = b → α},   ⨅ x, ⨅ (h : x = b), f x h = f b ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vanishingIdeal_singleton (x : ProjectiveSpectrum 𝒜) :
    vanishingIdeal ({x} : Set (ProjectiveSpectrum 𝒜)) = x.asHomogeneousIdeal := by
  simp [vanishingIdeal]
/-
**ProjectiveSpectrum.subset_zeroLocus_iff_le_vanishingIdeal** 是 Mathlib 中的一个定理，位
于命名空间 `ProjectiveSpectrum`。
形式化陈述：subset_zeroLocus_iff_le_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (I
 : Ideal A) : t subseteq zeroLocus 𝒜 I ↔ I <= (vanishingIdeal t).toIdeal
参数：t : Set (ProjectiveSpectrum 𝒜)；I : Ideal A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProjectiveSpectrum.mem_vanishingIdeal`：mem_vanishingIdeal (t : Set (Proj
ectiveSpectrum 𝒜)) (f : A) : f in vanishingIdeal t ↔ forall x : ProjectiveSpectr
um 𝒜, x in t -> f in x.asHo…
· 使用定理 `ProjectiveSpectrum.mem_zeroLocus`：mem_zeroLocus (x : ProjectiveSpectrum 
𝒜) (s : Set A) : x in zeroLocus 𝒜 s ↔ s subseteq x.asHomogeneousIdeal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A) :
    t ⊆ zeroLocus 𝒜 I ↔ I ≤ (vanishingIdeal t).toIdeal :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _ _).mpr (h j) k, fun h =>
    fun x j =>
    (mem_zeroLocus _ _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

variable (𝒜)

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
/-
**ProjectiveSpectrum.gc_ideal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：gc_ideal : @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ 
(fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal t).toIdeal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProjectiveSpectrum.subset_zeroLocus_iff_le_vanishingIdeal`：subset_zeroLo
cus_iff_le_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A) : t sub
seteq zeroLocus 𝒜 I ↔ I <= (vanishingIdeal t).t…

--- 原说明 ---
`zeroLocus` and `vanishingIdeal` form a Galois connection.
-/
theorem gc_ideal :
    @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal t).toIdeal :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

set_option backward.isDefEq.respectTransparency.types false in
/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
/-
**ProjectiveSpectrum.gc_set** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：gc_set : @GaloisConnection (Set A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun
 s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProjectiveSpectrum.zeroLocus_span`：zeroLocus_span (s : Set A) : zeroLocu
s 𝒜 (Ideal.span s) = zeroLocus 𝒜 s
· 使用定理 `GaloisConnection.compose`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {l1 : α → β}   {u1 : 
β → α} {l2 : β…
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal

--- 原说明 ---
`zeroLocus` and `vanishingIdeal` form a Galois connection.
-/
theorem gc_set :
    @GaloisConnection (Set A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi A _).gc
  simpa [zeroLocus_span, Function.comp_def] using GaloisConnection.compose ideal_gc (gc_ideal 𝒜)
/-
**ProjectiveSpectrum.gc_homogeneousIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSp
ectrum`。
形式化陈述：gc_homogeneousIdeal : @GaloisConnection (HomogeneousIdeal 𝒜) (Set (Project
iveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => vanishingIdeal t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `ProjectiveSpectrum.subset_zeroLocus_iff_le_vanishingIdeal`：subset_zeroLo
cus_iff_le_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A) : t sub
seteq zeroLocus 𝒜 I ↔ I <= (vanishingIdeal t).t…
-/
theorem gc_homogeneousIdeal :
    @GaloisConnection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => zeroLocus 𝒜 I) fun t => vanishingIdeal t :=
  fun I t => by
  simpa [show I.toIdeal ≤ (vanishingIdeal t).toIdeal ↔ I ≤ vanishingIdeal t from Iff.rfl] using!
    subset_zeroLocus_iff_le_vanishingIdeal t I.toIdeal
/-
**ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal** 是 Mathlib 中的一个
定理，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)
) (s : Set A) : t subseteq zeroLocus 𝒜 s ↔ s subseteq vanishingIdeal t
参数：t : Set (ProjectiveSpectrum 𝒜)；s : Set A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProjectiveSpectrum.gc_set`：gc_set : @GaloisConnection (Set A) (Set (Proj
ectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
-/
theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (s : Set A) :
    t ⊆ zeroLocus 𝒜 s ↔ s ⊆ vanishingIdeal t :=
  (gc_set _) s t
/-
**ProjectiveSpectrum.subset_vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `
ProjectiveSpectrum`。
形式化陈述：subset_vanishingIdeal_zeroLocus (s : Set A) : s subseteq vanishingIdeal (z
eroLocus 𝒜 s)
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `ProjectiveSpectrum.gc_set`：gc_set : @GaloisConnection (Set A) (Set (Proj
ectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
-/
theorem subset_vanishingIdeal_zeroLocus (s : Set A) : s ⊆ vanishingIdeal (zeroLocus 𝒜 s) :=
  (gc_set _).le_u_l s
/-
**ProjectiveSpectrum.ideal_le_vanishingIdeal_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间
 `ProjectiveSpectrum`。
形式化陈述：ideal_le_vanishingIdeal_zeroLocus (I : Ideal A) : I <= (vanishingIdeal (ze
roLocus 𝒜 I)).toIdeal
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem ideal_le_vanishingIdeal_zeroLocus (I : Ideal A) :
    I ≤ (vanishingIdeal (zeroLocus 𝒜 I)).toIdeal :=
  (gc_ideal _).le_u_l I
/-
**ProjectiveSpectrum.homogeneousIdeal_le_vanishingIdeal_zeroLocus** 是 Mathlib 中的
一个定理，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : HomogeneousIdeal 𝒜) : I 
<= vanishingIdeal (zeroLocus 𝒜 I)
参数：I : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `ProjectiveSpectrum.gc_homogeneousIdeal`：gc_homogeneousIdeal : @GaloisCon
nection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLo
cus 𝒜 I) fun t => vanishingI…
-/
theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : HomogeneousIdeal 𝒜) :
    I ≤ vanishingIdeal (zeroLocus 𝒜 I) :=
  (gc_homogeneousIdeal _).le_u_l I
/-
**ProjectiveSpectrum.subset_zeroLocus_vanishingIdeal** 是 Mathlib 中的一个定理，位于命名空间 `
ProjectiveSpectrum`。
形式化陈述：subset_zeroLocus_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : t subse
teq zeroLocus 𝒜 (vanishingIdeal t)
参数：t : Set (ProjectiveSpectrum 𝒜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem subset_zeroLocus_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    t ⊆ zeroLocus 𝒜 (vanishingIdeal t) :=
  (gc_ideal _).l_u_le t
/-
**ProjectiveSpectrum.zeroLocus_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSp
ectrum`。
形式化陈述：zeroLocus_anti_mono {s t : Set A} (h : s subseteq t) : zeroLocus 𝒜 t subse
teq zeroLocus 𝒜 s
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `ProjectiveSpectrum.gc_set`：gc_set : @GaloisConnection (Set A) (Set (Proj
ectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
-/
theorem zeroLocus_anti_mono {s t : Set A} (h : s ⊆ t) : zeroLocus 𝒜 t ⊆ zeroLocus 𝒜 s :=
  (gc_set _).monotone_l h
/-
**ProjectiveSpectrum.zeroLocus_anti_mono_ideal** 是 Mathlib 中的一个定理，位于命名空间 `Projec
tiveSpectrum`。
形式化陈述：zeroLocus_anti_mono_ideal {s t : Ideal A} (h : s <= t) : zeroLocus 𝒜 (t : 
Set A) subseteq zeroLocus 𝒜 (s : Set A)
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem zeroLocus_anti_mono_ideal {s t : Ideal A} (h : s ≤ t) :
    zeroLocus 𝒜 (t : Set A) ⊆ zeroLocus 𝒜 (s : Set A) :=
  (gc_ideal _).monotone_l h
/-
**ProjectiveSpectrum.zeroLocus_anti_mono_homogeneousIdeal** 是 Mathlib 中的一个定理，位于命
名空间 `ProjectiveSpectrum`。
形式化陈述：zeroLocus_anti_mono_homogeneousIdeal {s t : HomogeneousIdeal 𝒜} (h : s <= 
t) : zeroLocus 𝒜 (t : Set A) subseteq zeroLocus 𝒜 (s : Set A)
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `ProjectiveSpectrum.gc_homogeneousIdeal`：gc_homogeneousIdeal : @GaloisCon
nection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLo
cus 𝒜 I) fun t => vanishingI…
-/
theorem zeroLocus_anti_mono_homogeneousIdeal {s t : HomogeneousIdeal 𝒜} (h : s ≤ t) :
    zeroLocus 𝒜 (t : Set A) ⊆ zeroLocus 𝒜 (s : Set A) :=
  (gc_homogeneousIdeal _).monotone_l h
/-
**ProjectiveSpectrum.vanishingIdeal_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `Project
iveSpectrum`。
形式化陈述：vanishingIdeal_anti_mono {s t : Set (ProjectiveSpectrum 𝒜)} (h : s subsete
q t) : vanishingIdeal t <= vanishingIdeal s
参数：ProjectiveSpectrum 𝒜；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem vanishingIdeal_anti_mono {s t : Set (ProjectiveSpectrum 𝒜)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc_ideal _).monotone_u h
/-
**ProjectiveSpectrum.zeroLocus_bot** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：zeroLocus_bot : zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem zeroLocus_bot : zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ :=
  (gc_ideal 𝒜).l_bot

@[simp]
/-
**ProjectiveSpectrum.zeroLocus_singleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `Project
iveSpectrum`。
形式化陈述：zeroLocus_singleton_zero : zeroLocus 𝒜 ({0} : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProjectiveSpectrum.zeroLocus_bot`：zeroLocus_bot : zeroLocus 𝒜 ((⊥ : Idea
l A) : Set A) = Set.univ
-/
theorem zeroLocus_singleton_zero : zeroLocus 𝒜 ({0} : Set A) = Set.univ :=
  zeroLocus_bot _

@[simp]
/-
**ProjectiveSpectrum.zeroLocus_empty** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectr
um`。
形式化陈述：zeroLocus_empty : zeroLocus 𝒜 (∅ : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `ProjectiveSpectrum.gc_set`：gc_set : @GaloisConnection (Set A) (Set (Proj
ectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
-/
theorem zeroLocus_empty : zeroLocus 𝒜 (∅ : Set A) = Set.univ :=
  (gc_set 𝒜).l_bot

@[simp]
/-
**ProjectiveSpectrum.vanishingIdeal_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSp
ectrum`。
形式化陈述：vanishingIdeal_univ : vanishingIdeal (∅ : Set (ProjectiveSpectrum 𝒜)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem vanishingIdeal_univ : vanishingIdeal (∅ : Set (ProjectiveSpectrum 𝒜)) = ⊤ := by
  simpa using! (gc_ideal _).u_top
/-
**ProjectiveSpectrum.zeroLocus_empty_of_one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Proje
ctiveSpectrum`。
形式化陈述：zeroLocus_empty_of_one_mem {s : Set A} (h : (1 : A) in s) : zeroLocus 𝒜 s 
= ∅
参数：h : (1 : A) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem zeroLocus_empty_of_one_mem {s : Set A} (h : (1 : A) ∈ s) : zeroLocus 𝒜 s = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
    (inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top <|
      x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr <| hx h

@[simp]
/-
**ProjectiveSpectrum.zeroLocus_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `Projecti
veSpectrum`。
形式化陈述：zeroLocus_singleton_one : zeroLocus 𝒜 ({1} : Set A) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProjectiveSpectrum.zeroLocus_empty_of_one_mem`：zeroLocus_empty_of_one_me
m {s : Set A} (h : (1 : A) in s) : zeroLocus 𝒜 s = ∅
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem zeroLocus_singleton_one : zeroLocus 𝒜 ({1} : Set A) = ∅ :=
  zeroLocus_empty_of_one_mem 𝒜 (Set.mem_singleton (1 : A))

@[simp]
/-
**ProjectiveSpectrum.zeroLocus_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectru
m`。
形式化陈述：zeroLocus_univ : zeroLocus 𝒜 (Set.univ : Set A) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProjectiveSpectrum.zeroLocus_empty_of_one_mem`：zeroLocus_empty_of_one_me
m {s : Set A} (h : (1 : A) in s) : zeroLocus 𝒜 s = ∅
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem zeroLocus_univ : zeroLocus 𝒜 (Set.univ : Set A) = ∅ :=
  zeroLocus_empty_of_one_mem _ (Set.mem_univ 1)
/-
**ProjectiveSpectrum.zeroLocus_sup_ideal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSp
ectrum`。
形式化陈述：zeroLocus_sup_ideal (I J : Ideal A) : zeroLocus 𝒜 ((I ⊔ J : Ideal A) : Set
 A) = zeroLocus _ I inter zeroLocus _ J
参数：I J : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem zeroLocus_sup_ideal (I J : Ideal A) :
    zeroLocus 𝒜 ((I ⊔ J : Ideal A) : Set A) = zeroLocus _ I ∩ zeroLocus _ J :=
  (gc_ideal 𝒜).l_sup
/-
**ProjectiveSpectrum.zeroLocus_sup_homogeneousIdeal** 是 Mathlib 中的一个定理，位于命名空间 `P
rojectiveSpectrum`。
形式化陈述：zeroLocus_sup_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) : zeroLocus 𝒜 ((
I ⊔ J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus _ I inter zeroLocus _ J
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `ProjectiveSpectrum.gc_homogeneousIdeal`：gc_homogeneousIdeal : @GaloisCon
nection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLo
cus 𝒜 I) fun t => vanishingI…
-/
theorem zeroLocus_sup_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 ((I ⊔ J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus _ I ∩ zeroLocus _ J :=
  (gc_homogeneousIdeal 𝒜).l_sup
/-
**ProjectiveSpectrum.zeroLocus_union** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectr
um`。
形式化陈述：zeroLocus_union (s s' : Set A) : zeroLocus 𝒜 (s union s') = zeroLocus _ s 
inter zeroLocus _ s'
参数：s s' : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `ProjectiveSpectrum.gc_set`：gc_set : @GaloisConnection (Set A) (Set (Proj
ectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
-/
theorem zeroLocus_union (s s' : Set A) : zeroLocus 𝒜 (s ∪ s') = zeroLocus _ s ∩ zeroLocus _ s' :=
  (gc_set 𝒜).l_sup
/-
**ProjectiveSpectrum.vanishingIdeal_union** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveS
pectrum`。
形式化陈述：vanishingIdeal_union (t t' : Set (ProjectiveSpectrum 𝒜)) : vanishingIdeal 
(t union t') = vanishingIdeal t ⊓ vanishingIdeal t'
参数：t t' : Set (ProjectiveSpectrum 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.ext`：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h
 : I.toIdeal = J.toIdeal) : I = J
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem vanishingIdeal_union (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' := by
  ext1; exact (gc_ideal 𝒜).u_inf
/-
**ProjectiveSpectrum.zeroLocus_iSup_ideal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveS
pectrum`。
形式化陈述：zeroLocus_iSup_ideal {γ : Sort*} (I : γ -> Ideal A) : zeroLocus _ ((⨆ i, I
 i : Ideal A) : Set A) = ⋂ i, zeroLocus 𝒜 (I i)
参数：I : γ -> Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem zeroLocus_iSup_ideal {γ : Sort*} (I : γ → Ideal A) :
    zeroLocus _ ((⨆ i, I i : Ideal A) : Set A) = ⋂ i, zeroLocus 𝒜 (I i) :=
  (gc_ideal 𝒜).l_iSup
/-
**ProjectiveSpectrum.zeroLocus_iSup_homogeneousIdeal** 是 Mathlib 中的一个定理，位于命名空间 `
ProjectiveSpectrum`。
形式化陈述：zeroLocus_iSup_homogeneousIdeal {γ : Sort*} (I : γ -> HomogeneousIdeal 𝒜) 
: zeroLocus _ ((⨆ i, I i : HomogeneousIdeal 𝒜) : Set A) = ⋂ i, zeroLocus 𝒜 (I i)
参数：I : γ -> HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `ProjectiveSpectrum.gc_homogeneousIdeal`：gc_homogeneousIdeal : @GaloisCon
nection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLo
cus 𝒜 I) fun t => vanishingI…
-/
theorem zeroLocus_iSup_homogeneousIdeal {γ : Sort*} (I : γ → HomogeneousIdeal 𝒜) :
    zeroLocus _ ((⨆ i, I i : HomogeneousIdeal 𝒜) : Set A) = ⋂ i, zeroLocus 𝒜 (I i) :=
  (gc_homogeneousIdeal 𝒜).l_iSup
/-
**ProjectiveSpectrum.zeroLocus_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpect
rum`。
形式化陈述：zeroLocus_iUnion {γ : Sort*} (s : γ -> Set A) : zeroLocus 𝒜 (⋃ i, s i) = ⋂
 i, zeroLocus 𝒜 (s i)
参数：s : γ -> Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `ProjectiveSpectrum.gc_set`：gc_set : @GaloisConnection (Set A) (Set (Proj
ectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t
-/
theorem zeroLocus_iUnion {γ : Sort*} (s : γ → Set A) :
    zeroLocus 𝒜 (⋃ i, s i) = ⋂ i, zeroLocus 𝒜 (s i) :=
  (gc_set 𝒜).l_iSup
/-
**ProjectiveSpectrum.zeroLocus_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpect
rum`。
形式化陈述：zeroLocus_bUnion (s : Set (Set A)) : zeroLocus 𝒜 (⋃ s' in s, s' : Set A) =
 ⋂ s' in s, zeroLocus 𝒜 s'
参数：s : Set (Set A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.zeroLocus_iUnion`：zeroLocus_iUnion {γ : Sort*} (s : γ
 -> Set A) : zeroLocus 𝒜 (⋃ i, s i) = ⋂ i, zeroLocus 𝒜 (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeroLocus_bUnion (s : Set (Set A)) :
    zeroLocus 𝒜 (⋃ s' ∈ s, s' : Set A) = ⋂ s' ∈ s, zeroLocus 𝒜 s' := by
  simp only [zeroLocus_iUnion]
/-
**ProjectiveSpectrum.vanishingIdeal_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Projective
Spectrum`。
形式化陈述：vanishingIdeal_iUnion {γ : Sort*} (t : γ -> Set (ProjectiveSpectrum 𝒜)) : 
vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i)
参数：t : γ -> Set (ProjectiveSpectrum 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.toIdeal_injective`：HomogeneousIdeal.toIdeal_injective :
 Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousIdeal.toIdeal_iInf`：toIdeal_iInf {κ : Sort*} (s : κ -> Homoge
neousIdeal 𝒜) : (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
-/
theorem vanishingIdeal_iUnion {γ : Sort*} (t : γ → Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  HomogeneousIdeal.toIdeal_injective <| by
    convert! (gc_ideal 𝒜).u_iInf; exact HomogeneousIdeal.toIdeal_iInf _
/-
**ProjectiveSpectrum.zeroLocus_inf** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：zeroLocus_inf (I J : Ideal A) : zeroLocus 𝒜 ((I ⊓ J : Ideal A) : Set A) = 
zeroLocus 𝒜 I union zeroLocus 𝒜 J
参数：I J : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.IsPrime.inf_le`：∀ {R : Type u} [inst : CommSemiring R] {I J P : Id
eal R}, P.IsPrime → (I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P)
· 使用定理 `ProjectiveSpectrum.isPrime`：∀ {A : Type u_1} {σ : Type u_2} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ → σ}   [i
nst_3 : GradedRi…
-/
theorem zeroLocus_inf (I J : Ideal A) :
    zeroLocus 𝒜 ((I ⊓ J : Ideal A) : Set A) = zeroLocus 𝒜 I ∪ zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.inf_le
/-
**ProjectiveSpectrum.union_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectr
um`。
形式化陈述：union_zeroLocus (s s' : Set A) : zeroLocus 𝒜 s union zeroLocus 𝒜 s' = zero
Locus 𝒜 (Ideal.span s ⊓ Ideal.span s' : Ideal A)
参数：s s' : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.zeroLocus_inf`：zeroLocus_inf (I J : Ideal A) : zeroLo
cus 𝒜 ((I ⊓ J : Ideal A) : Set A) = zeroLocus 𝒜 I union zeroLocus 𝒜 J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProjectiveSpectrum.zeroLocus_span`：zeroLocus_span (s : Set A) : zeroLocu
s 𝒜 (Ideal.span s) = zeroLocus 𝒜 s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_zeroLocus (s s' : Set A) :
    zeroLocus 𝒜 s ∪ zeroLocus 𝒜 s' = zeroLocus 𝒜 (Ideal.span s ⊓ Ideal.span s' : Ideal A) := by
  rw [zeroLocus_inf]
  simp
/-
**ProjectiveSpectrum.zeroLocus_mul_ideal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSp
ectrum`。
形式化陈述：zeroLocus_mul_ideal (I J : Ideal A) : zeroLocus 𝒜 ((I * J : Ideal A) : Set
 A) = zeroLocus 𝒜 I union zeroLocus 𝒜 J
参数：I J : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsPrime.mul_le`：∀ {R : Type u} [inst : CommSemiring R] {I J P : Id
eal R}, P.IsPrime → (I * J ≤ P ↔ I ≤ P ∨ J ≤ P)
· 使用定理 `ProjectiveSpectrum.isPrime`：∀ {A : Type u_1} {σ : Type u_2} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ → σ}   [i
nst_3 : GradedRi…
-/
theorem zeroLocus_mul_ideal (I J : Ideal A) :
    zeroLocus 𝒜 ((I * J : Ideal A) : Set A) = zeroLocus 𝒜 I ∪ zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.mul_le
/-
**ProjectiveSpectrum.zeroLocus_mul_homogeneousIdeal** 是 Mathlib 中的一个定理，位于命名空间 `P
rojectiveSpectrum`。
形式化陈述：zeroLocus_mul_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) : zeroLocus 𝒜 ((
I * J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus 𝒜 I union zeroLocus 𝒜 J
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.IsPrime.mul_le`：∀ {R : Type u} [inst : CommSemiring R] {I J P : Id
eal R}, P.IsPrime → (I * J ≤ P ↔ I ≤ P ∨ J ≤ P)
· 使用定理 `ProjectiveSpectrum.isPrime`：∀ {A : Type u_1} {σ : Type u_2} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ → σ}   [i
nst_3 : GradedRi…
-/
theorem zeroLocus_mul_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 ((I * J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus 𝒜 I ∪ zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.mul_le
/-
**ProjectiveSpectrum.zeroLocus_singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `Projecti
veSpectrum`。
形式化陈述：zeroLocus_singleton_mul (f g : A) : zeroLocus 𝒜 ({f * g} : Set A) = zeroLo
cus 𝒜 {f} union zeroLocus 𝒜 {g}
参数：f g : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsPrime.mul_mem_iff_mem_or_mem`：∀ {α : Type u} [inst : Semiring α]
 {I : Ideal α} [I.IsTwoSided], I.IsPrime → ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ 
I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `ProjectiveSpectrum.isPrime`：∀ {A : Type u_1} {σ : Type u_2} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ → σ}   [i
nst_3 : GradedRi…
-/
theorem zeroLocus_singleton_mul (f g : A) :
    zeroLocus 𝒜 ({f * g} : Set A) = zeroLocus 𝒜 {f} ∪ zeroLocus 𝒜 {g} :=
  Set.ext fun x => by simpa using x.isPrime.mul_mem_iff_mem_or_mem

@[simp]
/-
**ProjectiveSpectrum.zeroLocus_singleton_pow** 是 Mathlib 中的一个定理，位于命名空间 `Projecti
veSpectrum`。
形式化陈述：zeroLocus_singleton_pow (f : A) (n : Nat) (hn : 0 < n) : zeroLocus 𝒜 ({f ^
 n} : Set A) = zeroLocus 𝒜 {f}
参数：f : A；n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `ProjectiveSpectrum.isPrime`：∀ {A : Type u_1} {σ : Type u_2} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ → σ}   [i
nst_3 : GradedRi…
-/
theorem zeroLocus_singleton_pow (f : A) (n : ℕ) (hn : 0 < n) :
    zeroLocus 𝒜 ({f ^ n} : Set A) = zeroLocus 𝒜 {f} :=
  Set.ext fun x => by simpa using x.isPrime.pow_mem_iff_mem n hn
/-
**ProjectiveSpectrum.sup_vanishingIdeal_le** 是 Mathlib 中的一个定理，位于命名空间 `Projective
Spectrum`。
形式化陈述：sup_vanishingIdeal_le (t t' : Set (ProjectiveSpectrum 𝒜)) : vanishingIdeal
 t ⊔ vanishingIdeal t' <= vanishingIdeal (t inter t')
参数：t t' : Set (ProjectiveSpectrum 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousIdeal.mem_iff`：HomogeneousIdeal.mem_iff {I : HomogeneousIdeal
 𝒜} {x : A} : x in I.toIdeal ↔ x in I
· 使用定理 `HomogeneousIdeal.toIdeal_sup`：toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (
I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal
· 使用定理 `ProjectiveSpectrum.mem_vanishingIdeal`：mem_vanishingIdeal (t : Set (Proj
ectiveSpectrum 𝒜)) (f : A) : f in vanishingIdeal t ↔ forall x : ProjectiveSpectr
um 𝒜, x in t -> f in x.asHo…
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
theorem sup_vanishingIdeal_le (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal t ⊔ vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_sup, mem_vanishingIdeal,
    Submodule.mem_sup]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [HomogeneousIdeal.mem_iff, mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim
/-
**ProjectiveSpectrum.mem_compl_zeroLocus_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `P
rojectiveSpectrum`。
形式化陈述：mem_compl_zeroLocus_iff_notMem {f : A} {I : ProjectiveSpectrum 𝒜} : I in (
zeroLocus 𝒜 {f} : Set (ProjectiveSpectrum 𝒜))ᶜ ↔ f ∉ I.asHomogeneousIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `ProjectiveSpectrum.mem_zeroLocus`：mem_zeroLocus (x : ProjectiveSpectrum 
𝒜) (s : Set A) : x in zeroLocus 𝒜 s ↔ s subseteq x.asHomogeneousIdeal
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_compl_zeroLocus_iff_notMem {f : A} {I : ProjectiveSpectrum 𝒜} :
    I ∈ (zeroLocus 𝒜 {f} : Set (ProjectiveSpectrum 𝒜))ᶜ ↔ f ∉ I.asHomogeneousIdeal := by
  rw [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

/-- The Zariski topology on the prime spectrum of a commutative ring is defined via the closed sets
of the topology: they are exactly those sets that are the zero locus of a subset of the ring. -/
/-
**ProjectiveSpectrum.zariskiTopology** 是 Mathlib 中的一个实例，位于命名空间 `ProjectiveSpectr
um`。
形式化陈述：zariskiTopology : TopologicalSpace (ProjectiveSpectrum 𝒜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zariski topology on the prime spectrum of a commutative ring is defined via 
the closed sets
of the topology: they are exactly those sets that are the zero locus of a subset
 of the ring.
-/
instance zariskiTopology : TopologicalSpace (ProjectiveSpectrum 𝒜) :=
  TopologicalSpace.ofClosed (Set.range (ProjectiveSpectrum.zeroLocus 𝒜)) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      let f : Zs → Set _ := fun i => Classical.choose (h i.2)
      have H : (Set.iInter fun i ↦ zeroLocus 𝒜 (f i)) ∈ Set.range (zeroLocus 𝒜) :=
        ⟨_, zeroLocus_iUnion 𝒜 _⟩
      convert! H using 2
      funext i
      exact (Classical.choose_spec (h i.2)).symm)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus 𝒜 s t).symm⟩)

/-- The underlying topology of `Proj` is the projective spectrum of graded ring `A`. -/
/-
**ProjectiveSpectrum.top** 是 Mathlib 中的一个定义，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：top : TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying topology of `Proj` is the projective spectrum of graded ring `A`.
-/
def top : TopCat :=
  TopCat.of (ProjectiveSpectrum 𝒜)
/-
**ProjectiveSpectrum.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：isOpen_iff (U : Set (ProjectiveSpectrum 𝒜)) : IsOpen U ↔ exists s, Uᶜ = ze
roLocus 𝒜 s
参数：U : Set (ProjectiveSpectrum 𝒜)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_iff (U : Set (ProjectiveSpectrum 𝒜)) : IsOpen U ↔ ∃ s, Uᶜ = zeroLocus 𝒜 s := by
  simp only [@eq_comm _ Uᶜ]; rfl
/-
**ProjectiveSpectrum.isClosed_iff_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `Projectiv
eSpectrum`。
形式化陈述：isClosed_iff_zeroLocus (Z : Set (ProjectiveSpectrum 𝒜)) : IsClosed Z ↔ exi
sts s, Z = zeroLocus 𝒜 s
参数：Z : Set (ProjectiveSpectrum 𝒜)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `ProjectiveSpectrum.isOpen_iff`：isOpen_iff (U : Set (ProjectiveSpectrum 𝒜
)) : IsOpen U ↔ exists s, Uᶜ = zeroLocus 𝒜 s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff_zeroLocus (Z : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed Z ↔ ∃ s, Z = zeroLocus 𝒜 s := by rw [← isOpen_compl_iff, isOpen_iff, compl_compl]
/-
**ProjectiveSpectrum.isClosed_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpe
ctrum`。
形式化陈述：isClosed_zeroLocus (s : Set A) : IsClosed (zeroLocus 𝒜 s)
参数：s : Set A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.isClosed_iff_zeroLocus`：isClosed_iff_zeroLocus (Z : S
et (ProjectiveSpectrum 𝒜)) : IsClosed Z ↔ exists s, Z = zeroLocus 𝒜 s
-/
theorem isClosed_zeroLocus (s : Set A) : IsClosed (zeroLocus 𝒜 s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩
/-
**ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure** 是 Mathlib 中的一个定理，位于命名
空间 `ProjectiveSpectrum`。
形式化陈述：zeroLocus_vanishingIdeal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) : zer
oLocus 𝒜 (vanishingIdeal t : Set A) = closure t
参数：t : Set (ProjectiveSpectrum 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.isClosed_iff_zeroLocus`：isClosed_iff_zeroLocus (Z : S
et (ProjectiveSpectrum 𝒜)) : IsClosed Z ↔ exists s, Z = zeroLocus 𝒜 s
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal`：subset_ze
roLocus_iff_subset_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (s : Set A) :
 t subseteq zeroLocus 𝒜 s ↔ s subseteq vanishingIde…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `ProjectiveSpectrum.isClosed_zeroLocus`：isClosed_zeroLocus (s : Set A) : 
IsClosed (zeroLocus 𝒜 s)
· 使用定理 `ProjectiveSpectrum.subset_zeroLocus_vanishingIdeal`：subset_zeroLocus_van
ishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : t subseteq zeroLocus 𝒜 (vanishing
Ideal t)
-/
theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    zeroLocus 𝒜 (vanishingIdeal t : Set A) = closure t := by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zeroLocus 𝒜 s := by rwa [isClosed_iff_zeroLocus] at ht'
    rw [subset_zeroLocus_iff_subset_vanishingIdeal] at ht
    exact Set.Subset.trans ht hx
  · rw [(isClosed_zeroLocus _ _).closure_subset_iff]
    exact subset_zeroLocus_vanishingIdeal 𝒜 t
/-
**ProjectiveSpectrum.vanishingIdeal_closure** 是 Mathlib 中的一个定理，位于命名空间 `Projectiv
eSpectrum`。
形式化陈述：vanishingIdeal_closure (t : Set (ProjectiveSpectrum 𝒜)) : vanishingIdeal (
closure t) = vanishingIdeal t
参数：t : Set (ProjectiveSpectrum 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `ProjectiveSpectrum.gc_ideal`：gc_ideal : @GaloisConnection (Ideal A) (Set
 (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal
 t).toIdeal
· 使用定理 `HomogeneousIdeal.ext`：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h
 : I.toIdeal = J.toIdeal) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanish
ingIdeal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) : zeroLocus 𝒜 (vanishingIde
al t : Set A) = closure t
-/
theorem vanishingIdeal_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (closure t) = vanishingIdeal t := by
  have : (vanishingIdeal (zeroLocus 𝒜 (vanishingIdeal t))).toIdeal = _ := (gc_ideal 𝒜).u_l_u_eq_u t
  ext1
  rw [zeroLocus_vanishingIdeal_eq_closure 𝒜 t] at this
  exact this

section BasicOpen

/-- `basicOpen r` is the open subset containing all prime ideals not containing `r`. -/
/-
**ProjectiveSpectrum.basicOpen** 是 Mathlib 中的一个定义，位于命名空间 `ProjectiveSpectrum`。
形式化陈述：basicOpen (r : A) : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) where ca
rrier
参数：r : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`basicOpen r` is the open subset containing all prime ideals not containing `r`.
-/
def basicOpen (r : A) : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) where
  carrier := { x | r ∉ x.asHomogeneousIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩

@[simp]
/-
**ProjectiveSpectrum.mem_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：mem_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) : x in basicOpen 𝒜 f ↔ f 
∉ x.asHomogeneousIdeal
参数：f : A；x : ProjectiveSpectrum 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl
/-
**ProjectiveSpectrum.mem_coe_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpec
trum`。
形式化陈述：mem_coe_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) : x in (↑(basicOpen 𝒜
 f) : Set (ProjectiveSpectrum 𝒜)) ↔ f ∉ x.asHomogeneousIdeal
参数：f : A；x : ProjectiveSpectrum 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ (↑(basicOpen 𝒜 f) : Set (ProjectiveSpectrum 𝒜)) ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl
/-
**ProjectiveSpectrum.isOpen_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpect
rum`。
形式化陈述：isOpen_basicOpen {a : A} : IsOpen (basicOpen 𝒜 a : Set (ProjectiveSpectrum
 𝒜))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
theorem isOpen_basicOpen {a : A} : IsOpen (basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜)) :=
  (basicOpen 𝒜 a).isOpen

@[simp]
/-
**ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl** 是 Mathlib 中的一个定理，位于命名空间 `Pro
jectiveSpectrum`。
形式化陈述：basicOpen_eq_zeroLocus_compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpe
ctrum 𝒜)) = (zeroLocus 𝒜 {r})ᶜ
参数：r : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem basicOpen_eq_zeroLocus_compl (r : A) :
    (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})ᶜ :=
  Set.ext fun x => by simp only [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[simp]
/-
**ProjectiveSpectrum.basicOpen_one** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：basicOpen_one : basicOpen 𝒜 (1 : A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_
compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})
ᶜ
· 使用定理 `ProjectiveSpectrum.zeroLocus_singleton_one`：zeroLocus_singleton_one : ze
roLocus 𝒜 ({1} : Set A) = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basicOpen_one : basicOpen 𝒜 (1 : A) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp

@[simp]
/-
**ProjectiveSpectrum.basicOpen_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectru
m`。
形式化陈述：basicOpen_zero : basicOpen 𝒜 (0 : A) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_
compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})
ᶜ
· 使用定理 `ProjectiveSpectrum.zeroLocus_singleton_zero`：zeroLocus_singleton_zero : 
zeroLocus 𝒜 ({0} : Set A) = Set.univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basicOpen_zero : basicOpen 𝒜 (0 : A) = ⊥ :=
  TopologicalSpace.Opens.ext <| by simp
/-
**ProjectiveSpectrum.basicOpen_mul** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：basicOpen_mul (f g : A) : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 
𝒜 g
参数：f g : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_
compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})
ᶜ
· 使用定理 `ProjectiveSpectrum.zeroLocus_singleton_mul`：zeroLocus_singleton_mul (f g
 : A) : zeroLocus 𝒜 ({f * g} : Set A) = zeroLocus 𝒜 {f} union zeroLocus 𝒜 {g}
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basicOpen_mul (f g : A) : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
  TopologicalSpace.Opens.ext <| by simp [zeroLocus_singleton_mul]
/-
**ProjectiveSpectrum.basicOpen_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Projective
Spectrum`。
形式化陈述：basicOpen_mul_le_left (f g : A) : basicOpen 𝒜 (f * g) <= basicOpen 𝒜 f
参数：f g : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.basicOpen_mul`：basicOpen_mul (f g : A) : basicOpen 𝒜 
(f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem basicOpen_mul_le_left (f g : A) : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 f := by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_left
/-
**ProjectiveSpectrum.basicOpen_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Projectiv
eSpectrum`。
形式化陈述：basicOpen_mul_le_right (f g : A) : basicOpen 𝒜 (f * g) <= basicOpen 𝒜 g
参数：f g : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.basicOpen_mul`：basicOpen_mul (f g : A) : basicOpen 𝒜 
(f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem basicOpen_mul_le_right (f g : A) : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 g := by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_right

@[simp]
/-
**ProjectiveSpectrum.basicOpen_pow** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpectrum
`。
形式化陈述：basicOpen_pow (f : A) (n : Nat) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basic
Open 𝒜 f
参数：f : A；n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_
compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})
ᶜ
· 使用定理 `ProjectiveSpectrum.zeroLocus_singleton_pow`：zeroLocus_singleton_pow (f :
 A) (n : Nat) (hn : 0 < n) : zeroLocus 𝒜 ({f ^ n} : Set A) = zeroLocus 𝒜 {f}
-/
theorem basicOpen_pow (f : A) (n : ℕ) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  TopologicalSpace.Opens.ext <| by simpa using zeroLocus_singleton_pow 𝒜 f n hn
/-
**ProjectiveSpectrum.basicOpen_eq_union_of_projection** 是 Mathlib 中的一个定理，位于命名空间 
`ProjectiveSpectrum`。
形式化陈述：basicOpen_eq_union_of_projection (f : A) : basicOpen 𝒜 f = ⨆ i : Nat, basi
cOpen 𝒜 (GradedRing.proj 𝒜 i f)
参数：f : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProjectiveSpectrum.mem_coe_basicOpen`：mem_coe_basicOpen (f : A) (x : Pro
jectiveSpectrum 𝒜) : x in (↑(basicOpen 𝒜 f) : Set (ProjectiveSpectrum 𝒜)) ↔ f ∉ 
x.asHomogeneousIdeal
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `TopologicalSpace.Opens.mem_sSup`：mem_sSup {Us : Set (Opens α)} {x : α} :
 x in sSup Us ↔ exists u in Us, x in u
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `ProjectiveSpectrum.mem_basicOpen`：mem_basicOpen (f : A) (x : ProjectiveS
pectrum 𝒜) : x in basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal
· 使用定理 `HomogeneousSubmodule.is_homogeneous'`：∀ {ιA : Type u_1} {ιM : Type u_2} 
{σA : Type u_3} {σM : Type u_4} {A : Type u_5} {M : Type u_6} [inst : Semiring A
]   [inst_1 : AddCommMonoi…
-/
theorem basicOpen_eq_union_of_projection (f : A) :
    basicOpen 𝒜 f = ⨆ i : ℕ, basicOpen 𝒜 (GradedRing.proj 𝒜 i f) :=
  TopologicalSpace.Opens.ext <|
    Set.ext fun z => by
      rw [mem_coe_basicOpen, mem_coe, iSup, TopologicalSpace.Opens.mem_sSup]
      constructor <;> intro hz
      · rcases show ∃ i, GradedRing.proj 𝒜 i f ∉ z.asHomogeneousIdeal by
          contrapose! hz with H
          classical
          rw [← DirectSum.sum_support_decompose 𝒜 f]
          apply Ideal.sum_mem _ fun i _ => H i with ⟨i, hi⟩
        exact ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i f), ⟨i, rfl⟩, by rwa [mem_basicOpen]⟩
      · obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
        exact fun rid => hz (z.1.2 i rid)
/-
**ProjectiveSpectrum.isTopologicalBasis_basic_opens** 是 Mathlib 中的一个定理，位于命名空间 `P
rojectiveSpectrum`。
形式化陈述：isTopologicalBasis_basic_opens : TopologicalSpace.IsTopologicalBasis (Set.
range fun r : A => (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `ProjectiveSpectrum.isOpen_basicOpen`：isOpen_basicOpen {a : A} : IsOpen (
basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `ProjectiveSpectrum.mem_zeroLocus`：mem_zeroLocus (x : ProjectiveSpectrum 
𝒜) (s : Set A) : x in zeroLocus 𝒜 s ↔ s subseteq x.asHomogeneousIdeal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_
compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})
ᶜ
· 使用定理 `ProjectiveSpectrum.zeroLocus_anti_mono`：zeroLocus_anti_mono {s t : Set A
} (h : s subseteq t) : zeroLocus 𝒜 t subseteq zeroLocus 𝒜 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : A => (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen 𝒜
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_iff, ← hs, mem_zeroLocus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen 𝒜 f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl, ← hs, basicOpen_eq_zeroLocus_compl, compl_compl]
    exact zeroLocus_anti_mono 𝒜 (Set.singleton_subset_iff.mpr hfs)

end BasicOpen

section Order

/-!
## The specialization order

We endow `ProjectiveSpectrum 𝒜` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.
-/


/-
**ProjectiveSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `ProjectiveSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## The specialization order

We endow `ProjectiveSpectrum 𝒜` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.
-/
instance : PartialOrder (ProjectiveSpectrum 𝒜) :=
  PartialOrder.lift asHomogeneousIdeal fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp only [mk.injEq, imp_self]

@[simp]
/-
**ProjectiveSpectrum.as_ideal_le_as_ideal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveS
pectrum`。
形式化陈述：as_ideal_le_as_ideal (x y : ProjectiveSpectrum 𝒜) : x.asHomogeneousIdeal <
= y.asHomogeneousIdeal ↔ x <= y
参数：x y : ProjectiveSpectrum 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem as_ideal_le_as_ideal (x y : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal ↔ x ≤ y :=
  Iff.rfl

@[simp]
/-
**ProjectiveSpectrum.as_ideal_lt_as_ideal** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveS
pectrum`。
形式化陈述：as_ideal_lt_as_ideal (x y : ProjectiveSpectrum 𝒜) : x.asHomogeneousIdeal <
 y.asHomogeneousIdeal ↔ x < y
参数：x y : ProjectiveSpectrum 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem as_ideal_lt_as_ideal (x y : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal < y.asHomogeneousIdeal ↔ x < y :=
  Iff.rfl
/-
**ProjectiveSpectrum.le_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `ProjectiveSpe
ctrum`。
形式化陈述：le_iff_mem_closure (x y : ProjectiveSpectrum 𝒜) : x <= y ↔ y in closure ({
x} : Set (ProjectiveSpectrum 𝒜))
参数：x y : ProjectiveSpectrum 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProjectiveSpectrum.as_ideal_le_as_ideal`：as_ideal_le_as_ideal (x y : Pro
jectiveSpectrum 𝒜) : x.asHomogeneousIdeal <= y.asHomogeneousIdeal ↔ x <= y
· 使用定理 `ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanish
ingIdeal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) : zeroLocus 𝒜 (vanishingIde
al t : Set A) = closure t
· 使用定理 `ProjectiveSpectrum.mem_zeroLocus`：mem_zeroLocus (x : ProjectiveSpectrum 
𝒜) (s : Set A) : x in zeroLocus 𝒜 s ↔ s subseteq x.asHomogeneousIdeal
· 使用定理 `ProjectiveSpectrum.vanishingIdeal_singleton`：vanishingIdeal_singleton (x
 : ProjectiveSpectrum 𝒜) : vanishingIdeal ({x} : Set (ProjectiveSpectrum 𝒜)) = x
.asHomogeneousIdeal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_iff_mem_closure (x y : ProjectiveSpectrum 𝒜) :
    x ≤ y ↔ y ∈ closure ({x} : Set (ProjectiveSpectrum 𝒜)) := by
  rw [← as_ideal_le_as_ideal, ← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus,
    vanishingIdeal_singleton]
  simp only [as_ideal_le_as_ideal, coe_subset_coe]

end Order

end ProjectiveSpectrum

