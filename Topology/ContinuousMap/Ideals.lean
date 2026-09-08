/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace

/-!
# Ideals of continuous functions

For a topological semiring `R` and a topological space `X` there is a Galois connection between
`Ideal C(X, R)` and `Set X` given by sending each `I : Ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : Set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `ContinuousMap.setOfIdeal` and
`ContinuousMap.idealOfSet`. As long as `R` is Hausdorff, `ContinuousMap.setOfIdeal I` is open,
and if, in addition, `X` is locally compact, then `ContinuousMap.setOfIdeal s` is closed.

When `R = 𝕜` with `RCLike 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, 𝕜)`. Because we do not have a bundled type of closed ideals,
we simply register this as a Galois insertion between `Ideal C(X, 𝕜)` and `opens X`, which is
`ContinuousMap.idealOpensGI`. Consequently, the maximal ideals of `C(X, 𝕜)` are precisely those
ideals corresponding to (complements of) singletons in `X`.

In addition, when `X` is locally compact and `𝕜` is a nontrivial topological integral domain, then
there is a natural continuous map from `X` to `WeakDual.characterSpace 𝕜 C(X, 𝕜)` given by point
evaluation, which is herein called `WeakDual.CharacterSpace.continuousMapEval`. Again, when `X` is
compact Hausdorff and `RCLike 𝕜`, more can be obtained. In particular, in that context this map is
bijective, and since the domain is compact and the codomain is Hausdorff, it is a homeomorphism,
herein called `WeakDual.CharacterSpace.homeoEval`.

## Main definitions

* `ContinuousMap.idealOfSet`: ideal of functions which vanish on the complement of a set.
* `ContinuousMap.setOfIdeal`: complement of the set on which all functions in the ideal vanish.
* `ContinuousMap.opensOfIdeal`: `ContinuousMap.setOfIdeal` as a term of `opens X`.
* `ContinuousMap.idealOpensGI`: The Galois insertion `ContinuousMap.opensOfIdeal` and
  `fun s ↦ ContinuousMap.idealOfSet ↑s`.
* `WeakDual.CharacterSpace.continuousMapEval`: the natural continuous map from a locally compact
  topological space `X` to the `WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point
  evaluation at `x`, with modest hypothesis on `𝕜`.
* `WeakDual.CharacterSpace.homeoEval`: this is `WeakDual.CharacterSpace.continuousMapEval`
  upgraded to a homeomorphism when `X` is compact Hausdorff and `RCLike 𝕜`.

## Main statements

* `ContinuousMap.idealOfSet_ofIdeal_eq_closure`: when `X` is compact Hausdorff and
  `RCLike 𝕜`, `idealOfSet 𝕜 (setOfIdeal I) = I.closure` for any ideal `I : Ideal C(X, 𝕜)`.
* `ContinuousMap.setOfIdeal_ofSet_eq_interior`: when `X` is compact Hausdorff and `RCLike 𝕜`,
  `setOfIdeal (idealOfSet 𝕜 s) = interior s` for any `s : Set X`.
* `ContinuousMap.ideal_isMaximal_iff`: when `X` is compact Hausdorff and `RCLike 𝕜`, a closed
  ideal of `C(X, 𝕜)` is maximal if and only if it is `idealOfSet 𝕜 {x}ᶜ` for some `x : X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`ContinuousMap.idealOpensGI`.

## Tags

ideal, continuous function, compact, Hausdorff
-/

@[expose] public section


open scoped NNReal

namespace ContinuousMap

open TopologicalSpace

section IsTopologicalRing

variable {X R : Type*} [TopologicalSpace X] [Semiring R]
variable [TopologicalSpace R] [IsTopologicalSemiring R]
variable (R)

/-- Given a topological ring `R` and `s : Set X`, construct the ideal in `C(X, R)` of functions
which vanish on the complement of `s`. -/
/-
**ContinuousMap.idealOfSet** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：idealOfSet (s : Set X) : Ideal C(X, R) where carrier
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a topological ring `R` and `s : Set X`, construct the ideal in `C(X, R)` o
f functions
which vanish on the complement of `s`.
-/
def idealOfSet (s : Set X) : Ideal C(X, R) where
  carrier := {f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf x hx := mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)
/-
**ContinuousMap.idealOfSet_closed** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：idealOfSet_closed [T2Space R] (s : Set X) : IsClosed (idealOfSet R s : Set
 C(X, R))
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `Submodule.mk.congr_simp`：∀ {R : Type u} {M : Type v} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (toAddSubmonoid toAdd
Submonoid_1 :…
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem idealOfSet_closed [T2Space R] (s : Set X) :
    IsClosed (idealOfSet R s : Set C(X, R)) := by
  simp only [idealOfSet, Submodule.coe_set_mk, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

variable {R}
/-
**ContinuousMap.mem_idealOfSet** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：mem_idealOfSet {s : Set X} {f : C(X, R)} : f in idealOfSet R s ↔ forall ⦃x
 : X⦄, x in sᶜ -> f x = 0
参数：X, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_idealOfSet {s : Set X} {f : C(X, R)} :
    f ∈ idealOfSet R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := by
  convert! Iff.rfl
/-
**ContinuousMap.notMem_idealOfSet** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：notMem_idealOfSet {s : Set X} {f : C(X, R)} : f ∉ idealOfSet R s ↔ exists 
x in sᶜ, f x != 0
参数：X, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_idealOfSet {s : Set X} {f : C(X, R)} : f ∉ idealOfSet R s ↔ ∃ x ∈ sᶜ, f x ≠ 0 := by
  simp_rw [mem_idealOfSet]; push Not; rfl

/-- Given an ideal `I` of `C(X, R)`, construct the set of points for which every function in the
ideal vanishes on the complement. -/
/-
**ContinuousMap.setOfIdeal** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：setOfIdeal (I : Ideal C(X, R)) : Set X
参数：I : Ideal C(X, R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `I` of `C(X, R)`, construct the set of points for which every fun
ction in the
ideal vanishes on the complement.
-/
def setOfIdeal (I : Ideal C(X, R)) : Set X :=
  {x : X | ∀ f ∈ I, (f : C(X, R)) x = 0}ᶜ
/-
**ContinuousMap.notMem_setOfIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：notMem_setOfIdeal {I : Ideal C(X, R)} {x : X} : x ∉ setOfIdeal I ↔ forall 
⦃f : C(X, R)⦄, f in I -> f x = 0
参数：X, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `ContinuousMap.setOfIdeal.eq_1`：∀ {X : Type u_1} {R : Type u_2} [inst : T
opologicalSpace X] [inst_1 : Semiring R] [inst_2 : TopologicalSpace R]   [inst_3
 : IsTopologicalSem…
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∉ setOfIdeal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 := by
  rw [← Set.mem_compl_iff, setOfIdeal, compl_compl, Set.mem_ofPred]
/-
**ContinuousMap.mem_setOfIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：mem_setOfIdeal {I : Ideal C(X, R)} {x : X} : x in setOfIdeal I ↔ exists f 
in I, (f : C(X, R)) x != 0
参数：X, R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∈ setOfIdeal I ↔ ∃ f ∈ I, (f : C(X, R)) x ≠ 0 := by
  simp_rw [setOfIdeal, Set.mem_compl_iff, Set.mem_ofPred]; push Not; rfl
/-
**ContinuousMap.setOfIdeal_open** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：setOfIdeal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (setOfIdeal I)
参数：I : Ideal C(X, R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem setOfIdeal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (setOfIdeal I) := by
  simp only [setOfIdeal, Set.ofPred_forall, isOpen_compl_iff]
  exact
    isClosed_iInter fun f =>
      isClosed_iInter fun _ => isClosed_eq (map_continuous f) continuous_const

/-- The open set `ContinuousMap.setOfIdeal I` realized as a term of `opens X`. -/
@[simps]
/-
**ContinuousMap.opensOfIdeal** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：opensOfIdeal [T2Space R] (I : Ideal C(X, R)) : Opens X
参数：I : Ideal C(X, R)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.setOfIdeal_open`：setOfIdeal_open [T2Space R] (I : Ideal C(
X, R)) : IsOpen (setOfIdeal I)

--- 原说明 ---
The open set `ContinuousMap.setOfIdeal I` realized as a term of `opens X`.
-/
def opensOfIdeal [T2Space R] (I : Ideal C(X, R)) : Opens X :=
  ⟨setOfIdeal I, setOfIdeal_open I⟩

@[simp]
/-
**ContinuousMap.setOfTop_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：setOfTop_eq_univ [Nontrivial R] : setOfIdeal (⊤ : Ideal C(X, R)) = Set.uni
v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.mem_setOfIdeal`：mem_setOfIdeal {I : Ideal C(X, R)} {x : X}
 : x in setOfIdeal I ↔ exists f in I, (f : C(X, R)) x != 0
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem setOfTop_eq_univ [Nontrivial R] : setOfIdeal (⊤ : Ideal C(X, R)) = Set.univ :=
  Set.univ_subset_iff.mp fun _ _ => mem_setOfIdeal.mpr ⟨1, Submodule.mem_top, one_ne_zero⟩

@[simp]
/-
**ContinuousMap.idealOfEmpty_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：idealOfEmpty_eq_bot : idealOfSet R (∅ : Set X) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem idealOfEmpty_eq_bot : idealOfSet R (∅ : Set X) = ⊥ :=
  Ideal.ext fun f => by
    simp only [mem_idealOfSet, Set.compl_empty, Set.mem_univ, forall_true_left, Ideal.mem_bot,
      DFunLike.ext_iff, zero_apply]

@[simp]
/-
**ContinuousMap.mem_idealOfSet_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMap`。
形式化陈述：mem_idealOfSet_compl_singleton (x : X) (f : C(X, R)) : f in idealOfSet R (
{x}ᶜ : Set X) ↔ f x = 0
参数：x : X；f : C(X, R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_idealOfSet_compl_singleton (x : X) (f : C(X, R)) :
    f ∈ idealOfSet R ({x}ᶜ : Set X) ↔ f x = 0 := by
  simp only [mem_idealOfSet, compl_compl, Set.mem_singleton_iff, forall_eq]

variable (X R)
/-
**ContinuousMap.ideal_gc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：ideal_gc : GaloisConnection (setOfIdeal : Ideal C(X, R) -> Set X) (idealOf
Set R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousMap.notMem_idealOfSet`：notMem_idealOfSet {s : Set X} {f : C(X,
 R)} : f ∉ idealOfSet R s ↔ exists x in sᶜ, f x != 0
· 使用定理 `ContinuousMap.notMem_setOfIdeal`：notMem_setOfIdeal {I : Ideal C(X, R)} {
x : X} : x ∉ setOfIdeal I ↔ forall ⦃f : C(X, R)⦄, f in I -> f x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `ContinuousMap.mem_setOfIdeal`：mem_setOfIdeal {I : Ideal C(X, R)} {x : X}
 : x in setOfIdeal I ↔ exists f in I, (f : C(X, R)) x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem ideal_gc : GaloisConnection (setOfIdeal : Ideal C(X, R) → Set X) (idealOfSet R) := by
  refine fun I s => ⟨fun h f hf => ?_, fun h x hx => ?_⟩
  · by_contra h'
    rcases notMem_idealOfSet.mp h' with ⟨x, hx, hfx⟩
    exact hfx (notMem_setOfIdeal.mp (mt (@h x) hx) hf)
  · obtain ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
    by_contra hx'
    exact notMem_idealOfSet.mpr ⟨x, hx', hfx⟩ (h hf)

end IsTopologicalRing

section RCLike

open RCLike

variable {X 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]

/-- An auxiliary lemma used in the proof of `ContinuousMap.idealOfSet_ofIdeal_eq_closure` which may
be useful on its own. -/
/-
**ContinuousMap.exists_mul_le_one_eqOn_ge** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：exists_mul_le_one_eqOn_ge (f : C(X, Real>=0)) {c : Real>=0} (hc : 0 < c) :
 exists g : C(X, Real>=0), (forall x : X, (g * f) x <= 1) ∧ {x : X | c <= f x}.E
qOn (g * f) 1
参数：f : C(X, Real>=0)；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `Continuous.inv₀`：Continuous.inv₀ (hf : Continuous f) (h0 : forall x, f x
 != 0) : Continuous f⁻¹
· 使用定理 `NNReal.instContinuousInv₀`：ContinuousInv₀ NNReal
· 使用定理 `Continuous.sup`：Continuous.sup [Max L] [ContinuousSup L] {f g : X -> L} 
(hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x ⊔ g x
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `LinearOrder.topologicalLattice`：∀ {L : Type u_1} [inst : TopologicalSpac
e L] [inst_1 : LinearOrder L] [OrderClosedTopology L], TopologicalLattice L
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1

--- 原说明 ---
An auxiliary lemma used in the proof of `ContinuousMap.idealOfSet_ofIdeal_eq_clo
sure` which may
be useful on its own.
-/
theorem exists_mul_le_one_eqOn_ge (f : C(X, ℝ≥0)) {c : ℝ≥0} (hc : 0 < c) :
    ∃ g : C(X, ℝ≥0), (∀ x : X, (g * f) x ≤ 1) ∧ {x : X | c ≤ f x}.EqOn (g * f) 1 :=
  ⟨{  toFun := (f ⊔ const X c)⁻¹
      continuous_toFun :=
        ((map_continuous f).sup <| map_continuous _).inv₀ fun _ => (hc.trans_le le_sup_right).ne' },
    fun x =>
    (inv_mul_le_iff₀ (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
    fun x hx => by
    simpa only [coe_const, mul_apply, coe_mk, Pi.inv_apply, Pi.sup_apply,
      Function.const_apply, sup_eq_left.mpr (Set.mem_ofPred.mp hx), ne_eq, Pi.one_apply]
      using inv_mul_cancel₀ (hc.trans_le hx).ne' ⟩

variable [CompactSpace X] [T2Space X]

@[simp]
/-
**ContinuousMap.idealOfSet_ofIdeal_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMap`。
形式化陈述：idealOfSet_ofIdeal_eq_closure (I : Ideal C(X, 𝕜)) : idealOfSet 𝕜 (setOfIde
al I) = I.closure
参数：I : Ideal C(X, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.nnnorm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous 
fun x =…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.subset_compl_iff_disjoint_left`：subset_compl_iff_disjoint_left : s s
ubseteq tᶜ ↔ Disjoint t s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `nnnorm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖₊
 = 0 ↔ a = 0
· 使用定理 `ContinuousMap.mem_idealOfSet`：mem_idealOfSet {s : Set X} {f : C(X, R)} :
 f in idealOfSet R s ↔ forall ⦃x : X⦄, x in sᶜ -> f x = 0
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
（共 141 条，此处仅展示前 30 条）
-/
theorem idealOfSet_ofIdeal_eq_closure (I : Ideal C(X, 𝕜)) :
    idealOfSet 𝕜 (setOfIdeal I) = I.closure := by
  /- Since `idealOfSet 𝕜 (setOfIdeal I)` is closed and contains `I`, it contains `I.closure`.
    For the reverse inclusion, given `f ∈ idealOfSet 𝕜 (setOfIdeal I)` and `(ε : ℝ≥0) > 0` it
    suffices to show that `f` is within `ε` of `I`. -/
  refine le_antisymm ?_
      ((idealOfSet_closed 𝕜 <| setOfIdeal I).closure_subset_iff.mpr fun f hf x hx =>
        notMem_setOfIdeal.mp hx hf)
  refine (fun f hf => Metric.mem_closure_iff.mpr fun ε hε => ?_)
  lift ε to ℝ≥0 using hε.lt.le
  replace hε := show (0 : ℝ≥0) < ε from hε
  simp_rw [dist_nndist]
  norm_cast
  -- Let `t := {x : X | ε / 2 ≤ ‖f x‖₊}}` which is closed and disjoint from `set_of_ideal I`.
  set t := {x : X | ε / 2 ≤ ‖f x‖₊}
  have ht : IsClosed t := isClosed_le continuous_const (map_continuous f).nnnorm
  have htI : Disjoint t (setOfIdeal I)ᶜ := by
    refine Set.subset_compl_iff_disjoint_left.mp fun x hx => ?_
    simpa only [t, Set.mem_ofPred, Set.mem_compl_iff, not_le] using!
      (nnnorm_eq_zero.mpr (mem_idealOfSet.mp hf hx)).trans_lt (half_pos hε)
  /- It suffices to produce `g : C(X, ℝ≥0)` which takes values in `[0,1]` and is constantly `1` on
    `t` such that when composed with the natural embedding of `ℝ≥0` into `𝕜` lies in the ideal `I`.
    Indeed, then `‖f - f * ↑g‖ ≤ ‖f * (1 - ↑g)‖ ≤ ⨆ ‖f * (1 - ↑g) x‖`. When `x ∉ t`, `‖f x‖ < ε / 2`
    and `‖(1 - ↑g) x‖ ≤ 1`, and when `x ∈ t`, `(1 - ↑g) x = 0`, and clearly `f * ↑g ∈ I`. -/
  suffices
    ∃ g : C(X, ℝ≥0), (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g ∈ I ∧ (∀ x, g x ≤ 1) ∧ t.EqOn g 1 by
    obtain ⟨g, hgI, hg, hgt⟩ := this
    refine ⟨f * (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g, I.mul_mem_left f hgI, ?_⟩
    rw [nndist_eq_nnnorm]
    refine (nnnorm_lt_iff _ hε).2 fun x => ?_
    simp only [coe_sub, coe_mul, Pi.sub_apply, Pi.mul_apply]
    by_cases hx : x ∈ t
    · simpa only [hgt hx, comp_apply, Pi.one_apply, ContinuousMap.coe_coe, algebraMapCLM_apply,
        map_one, mul_one, sub_self, nnnorm_zero] using! hε
    · refine lt_of_le_of_lt ?_ (half_lt_self hε)
      have :=
        calc
          ‖((1 - (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x : 𝕜)‖₊ =
              ‖1 - algebraMap ℝ≥0 𝕜 (g x)‖₊ := by
            simp only [coe_sub, coe_one, coe_comp, ContinuousMap.coe_coe, Pi.sub_apply,
              Pi.one_apply, Function.comp_apply, algebraMapCLM_apply]
          _ = ‖algebraMap ℝ≥0 𝕜 (1 - g x)‖₊ := by
            simp only [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, NNReal.coe_sub (hg x),
              NNReal.coe_one, sub_smul, one_smul]
          _ ≤ 1 := (nnnorm_algebraMap_nnreal 𝕜 (1 - g x)).trans_le tsub_le_self
      calc
        ‖f x - f x * (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g x‖₊ =
            ‖f x * (1 - (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x‖₊ := by
          simp only [mul_sub, coe_sub, coe_one, Pi.sub_apply, Pi.one_apply, mul_one]
        _ ≤ ε / 2 * ‖(1 - (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x‖₊ :=
          ((nnnorm_mul_le _ _).trans
            (mul_le_mul_left (not_le.mp <| show ¬ε / 2 ≤ ‖f x‖₊ from hx).le _))
        _ ≤ ε / 2 := by simpa only [mul_one] using! mul_le_mul_right this _
  /- There is some `g' : C(X, ℝ≥0)` which is strictly positive on `t` such that the composition
    `↑g` with the natural embedding of `ℝ≥0` into `𝕜` lies in `I`. This follows from compactness of
    `t` and that we can do it in any neighborhood of a point `x ∈ t`. Indeed, since `x ∈ t`, then
    `fₓ x ≠ 0` for some `fₓ ∈ I` and so `fun y ↦ ‖(star fₓ * fₓ) y‖₊` is strictly positive in a
    neighborhood of `y`. Moreover, `(‖(star fₓ * fₓ) y‖₊ : 𝕜) = (star fₓ * fₓ) y`, so composition of
    this map with the natural embedding is just `star fₓ * fₓ ∈ I`. -/
  have : ∃ g' : C(X, ℝ≥0), (algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g' ∈ I ∧ ∀ x ∈ t, 0 < g' x := by
    refine ht.isCompact.induction_on ?_ ?_ ?_ ?_
    · refine ⟨0, ?_, fun x hx => False.elim hx⟩
      convert! I.zero_mem
      ext
      simp only [comp_apply, zero_apply, ContinuousMap.coe_coe, map_zero]
    · rintro s₁ s₂ hs ⟨g, hI, hgt⟩; exact ⟨g, hI, fun x hx => hgt x (hs hx)⟩
    · rintro s₁ s₂ ⟨g₁, hI₁, hgt₁⟩ ⟨g₂, hI₂, hgt₂⟩
      refine ⟨g₁ + g₂, ?_, fun x hx => ?_⟩
      · convert! I.add_mem hI₁ hI₂
        ext y
        simp
      · rcases hx with (hx | hx)
        · simpa using add_lt_add_of_lt_of_le (hgt₁ x hx) zero_le
        · simpa using add_lt_add_of_le_of_lt zero_le (hgt₂ x hx)
    · intro x hx
      replace hx := htI.subset_compl_right hx
      rw [compl_compl, mem_setOfIdeal] at hx
      obtain ⟨g, hI, hgx⟩ := hx
      have := (map_continuous g).continuousAt.eventually_ne hgx
      refine
        ⟨{y : X | g y ≠ 0} ∩ t,
          mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨_, this, Set.Subset.rfl⟩,
          ⟨⟨fun x => ‖g x‖₊ ^ 2, (map_continuous g).nnnorm.fun_pow 2⟩, ?_, fun x hx =>
            pow_pos (norm_pos_iff.mpr hx.1) 2⟩⟩
      convert! I.mul_mem_left (star g) hI
      ext
      simp only [comp_apply, coe_mk, algebraMapCLM_apply, map_pow,
        mul_apply, star_apply, star_def]
      simp only [RCLike.conj_mul]
      rfl
  /- Get the function `g'` which is guaranteed to exist above. By the extreme value theorem and
    compactness of `t`, there is some `0 < c` such that `c ≤ g' x` for all `x ∈ t`. Then by
    `exists_mul_le_one_eqOn_ge` there is some `g` for which `g * g'` is the desired function. -/
  obtain ⟨g', hI', hgt'⟩ := this
  obtain ⟨c, hc, hgc'⟩ : ∃ c > 0, t ⊆ {y | c ≤ g' y} :=
    t.eq_empty_or_nonempty.elim
      (fun ht' => ⟨1, zero_lt_one, fun y hy => False.elim (by rwa [ht'] at hy)⟩) fun ht' =>
      let ⟨x, hx, hx'⟩ := ht.isCompact.exists_isMinOn ht' (map_continuous g').continuousOn
      ⟨g' x, hgt' x hx, hx'⟩
  obtain ⟨g, hg, hgc⟩ := exists_mul_le_one_eqOn_ge g' hc
  refine ⟨g * g', ?_, hg, hgc.mono hgc'⟩
  convert! I.mul_mem_left ((algebraMapCLM ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) hI'
  ext
  simp only [coe_algebraMapCLM, comp_apply, mul_apply, ContinuousMap.coe_coe, map_mul]
/-
**ContinuousMap.idealOfSet_ofIdeal_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMap`。
形式化陈述：idealOfSet_ofIdeal_isClosed {I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(
X, 𝕜))) : idealOfSet 𝕜 (setOfIdeal I) = I
参数：X, 𝕜；hI : IsClosed (I : Set C(X, 𝕜))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `ContinuousMap.idealOfSet_ofIdeal_eq_closure`：idealOfSet_ofIdeal_eq_closu
re (I : Ideal C(X, 𝕜)) : idealOfSet 𝕜 (setOfIdeal I) = I.closure
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem idealOfSet_ofIdeal_isClosed {I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜))) :
    idealOfSet 𝕜 (setOfIdeal I) = I :=
  (idealOfSet_ofIdeal_eq_closure I).trans (Ideal.ext <| Set.ext_iff.mp hI.closure_eq)

variable (𝕜)

@[simp]
/-
**ContinuousMap.setOfIdeal_ofSet_eq_interior** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：setOfIdeal_ofSet_eq_interior (s : Set X) : setOfIdeal (idealOfSet 𝕜 s) = i
nterior s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.subset_interior_iff`：IsOpen.subset_interior_iff (h₁ : IsOpen s) :
 s subseteq interior t ↔ s subseteq t
· 使用定理 `ContinuousMap.setOfIdeal_open`：setOfIdeal_open [T2Space R] (I : Ideal C(
X, R)) : IsOpen (setOfIdeal I)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousMap.mem_setOfIdeal`：mem_setOfIdeal {I : Ideal C(X, R)} {x : X}
 : x in setOfIdeal I ↔ exists f in I, (f : C(X, R)) x != 0
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
（共 41 条，此处仅展示前 30 条）
-/
theorem setOfIdeal_ofSet_eq_interior (s : Set X) : setOfIdeal (idealOfSet 𝕜 s) = interior s := by
  refine
    Set.Subset.antisymm
      ((setOfIdeal_open (idealOfSet 𝕜 s)).subset_interior_iff.mpr fun x hx =>
        let ⟨f, hf, hfx⟩ := mem_setOfIdeal.mp hx
        Set.notMem_compl_iff.mp (mt (@hf x) hfx))
      fun x hx => ?_
  -- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is zero on `sᶜ` and `f x ≠ 0`.
  rw [← compl_compl (interior s), ← closure_compl] at hx
  simp_rw [mem_setOfIdeal, mem_idealOfSet]
  /- Apply Urysohn's lemma to get `g : C(X, ℝ)` which is zero on `sᶜ` and `g x ≠ 0`, then compose
    with the natural embedding `ℝ ↪ 𝕜` to produce the desired `f`. -/
  obtain ⟨g, hgs, hgx : Set.EqOn g 1 {x}, -⟩ :=
    exists_continuous_zero_one_of_isClosed isClosed_closure isClosed_singleton
      (Set.disjoint_singleton_right.mpr hx)
  exact
    ⟨⟨fun x => g x, continuous_ofReal.comp (map_continuous g)⟩, by
      simpa only [coe_mk, ofReal_eq_zero] using! fun x hx => hgs (subset_closure hx), by
      simpa only [coe_mk, hgx (Set.mem_singleton x), Pi.one_apply, RCLike.ofReal_one] using!
        one_ne_zero⟩
/-
**ContinuousMap.setOfIdeal_ofSet_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：setOfIdeal_ofSet_of_isOpen {s : Set X} (hs : IsOpen s) : setOfIdeal (ideal
OfSet 𝕜 s) = s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousMap.setOfIdeal_ofSet_eq_interior`：setOfIdeal_ofSet_eq_interior
 (s : Set X) : setOfIdeal (idealOfSet 𝕜 s) = interior s
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem setOfIdeal_ofSet_of_isOpen {s : Set X} (hs : IsOpen s) : setOfIdeal (idealOfSet 𝕜 s) = s :=
  (setOfIdeal_ofSet_eq_interior 𝕜 s).trans hs.interior_eq

variable (X) in
/-- The Galois insertion `ContinuousMap.opensOfIdeal : Ideal C(X, 𝕜) → Opens X` and
`fun s ↦ ContinuousMap.idealOfSet ↑s`. -/
@[simps]
/-
**ContinuousMap.idealOpensGI** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：idealOpensGI : GaloisInsertion (opensOfIdeal : Ideal C(X, 𝕜) -> Opens X) f
un s => idealOfSet 𝕜 s where choice I _
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois insertion `ContinuousMap.opensOfIdeal : Ideal C(X, 𝕜) → Opens X` and
`fun s ↦ ContinuousMap.idealOfSet ↑s`.
-/
def idealOpensGI :
    GaloisInsertion (opensOfIdeal : Ideal C(X, 𝕜) → Opens X) fun s => idealOfSet 𝕜 s where
  choice I _ := opensOfIdeal I.closure
  gc I s := ideal_gc X 𝕜 I s
  le_l_u s := (setOfIdeal_ofSet_of_isOpen 𝕜 s.isOpen).ge
  choice_eq I hI :=
    congr_arg _ <|
      Ideal.ext
        (Set.ext_iff.mp
          (isClosed_of_closure_subset <|
              (idealOfSet_ofIdeal_eq_closure I ▸ hI : I.closure ≤ I)).closure_eq)
/-
**ContinuousMap.idealOfSet_isMaximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p`。
形式化陈述：idealOfSet_isMaximal_iff (s : Opens X) : (idealOfSet 𝕜 (s : Set X)).IsMaxi
mal ↔ IsCoatom s
参数：s : Opens X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `GaloisInsertion.isCoatom_iff`：isCoatom_iff [OrderTop α] [IsCoatomic α] [
OrderTop β] {l : α -> β} {u : β -> α} (gi : GaloisInsertion l u) (h_coatom : for
all a : α, IsCoato…
· 使用定理 `Ideal.instIsCoatomic`：∀ {α : Type u} [inst : Semiring α], IsCoatomic (Id
eal α)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousMap.idealOfSet_ofIdeal_isClosed`：idealOfSet_ofIdeal_isClosed {
I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜))) : idealOfSet 𝕜 (setOfIdeal 
I) = I
· 使用定理 `Ideal.IsMaximal.isClosed`：∀ {R : Type u_1} [inst : NormedRing R] [HasSum
mableGeomSeries R] {I : Ideal R} [hI : I.IsMaximal], IsClosed ↑I
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem idealOfSet_isMaximal_iff (s : Opens X) :
    (idealOfSet 𝕜 (s : Set X)).IsMaximal ↔ IsCoatom s := by
  rw [Ideal.isMaximal_def]
  refine (idealOpensGI X 𝕜).isCoatom_iff (fun I hI => ?_) s
  rw [← Ideal.isMaximal_def] at hI
  exact idealOfSet_ofIdeal_isClosed inferInstance
/-
**ContinuousMap.idealOf_compl_singleton_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousMap`。
形式化陈述：idealOf_compl_singleton_isMaximal (x : X) : (idealOfSet 𝕜 ({x}ᶜ : Set X)).
IsMaximal
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `ContinuousMap.idealOfSet_isMaximal_iff`：idealOfSet_isMaximal_iff (s : Op
ens X) : (idealOfSet 𝕜 (s : Set X)).IsMaximal ↔ IsCoatom s
· 使用定理 `TopologicalSpace.Opens.isCoatom_iff`：∀ {α : Type u_2} [inst : Topologica
lSpace α] [inst_1 : T1Space α] {s : TopologicalSpace.Opens α},   IsCoatom s ↔ ∃ 
x, s = {x}.compl
-/
theorem idealOf_compl_singleton_isMaximal (x : X) : (idealOfSet 𝕜 ({x}ᶜ : Set X)).IsMaximal :=
  (idealOfSet_isMaximal_iff 𝕜 _).mpr <| Opens.isCoatom_iff.mpr ⟨x, rfl⟩

variable {𝕜}
/-
**ContinuousMap.setOfIdeal_eq_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMap`。
形式化陈述：setOfIdeal_eq_compl_singleton (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal] : exi
sts x : X, setOfIdeal I = {x}ᶜ
参数：I : Ideal C(X, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.idealOfSet_ofIdeal_isClosed`：idealOfSet_ofIdeal_isClosed {
I : Ideal C(X, 𝕜)} (hI : IsClosed (I : Set C(X, 𝕜))) : idealOfSet 𝕜 (setOfIdeal 
I) = I
· 使用定理 `Ideal.IsMaximal.isClosed`：∀ {R : Type u_1} [inst : NormedRing R] [HasSum
mableGeomSeries R] {I : Ideal R} [hI : I.IsMaximal], IsClosed ↑I
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isCoatom_iff`：∀ {α : Type u_2} [inst : Topologica
lSpace α] [inst_1 : T1Space α] {s : TopologicalSpace.Opens α},   IsCoatom s ↔ ∃ 
x, s = {x}.compl
· 使用定理 `ContinuousMap.idealOfSet_isMaximal_iff`：idealOfSet_isMaximal_iff (s : Op
ens X) : (idealOfSet 𝕜 (s : Set X)).IsMaximal ↔ IsCoatom s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem setOfIdeal_eq_compl_singleton (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal] :
    ∃ x : X, setOfIdeal I = {x}ᶜ := by
  have h : (idealOfSet 𝕜 (setOfIdeal I)).IsMaximal :=
    (idealOfSet_ofIdeal_isClosed (inferInstance : IsClosed (I : Set C(X, 𝕜)))).symm ▸ hI
  obtain ⟨x, hx⟩ := Opens.isCoatom_iff.1 ((idealOfSet_isMaximal_iff 𝕜 (opensOfIdeal I)).1 h)
  exact ⟨x, congr_arg (fun (s : Opens X) => (s : Set X)) hx⟩
/-
**ContinuousMap.ideal_isMaximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：ideal_isMaximal_iff (I : Ideal C(X, 𝕜)) [hI : IsClosed (I : Set C(X, 𝕜))] 
: I.IsMaximal ↔ exists x : X, idealOfSet 𝕜 {x}ᶜ = I
参数：I : Ideal C(X, 𝕜)；I : Set C(X, 𝕜)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousMap.setOfIdeal_eq_compl_singleton`：setOfIdeal_eq_compl_singlet
on (I : Ideal C(X, 𝕜)) [hI : I.IsMaximal] : exists x : X, setOfIdeal I = {x}ᶜ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `ContinuousMap.idealOfSet_ofIdeal_eq_closure`：idealOfSet_ofIdeal_eq_closu
re (I : Ideal C(X, 𝕜)) : idealOfSet 𝕜 (setOfIdeal I) = I.closure
· 使用定理 `Ideal.closure_eq_of_isClosed`：Ideal.closure_eq_of_isClosed (I : Ideal R)
 (hI : IsClosed (I : Set R)) : I.closure = I
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.idealOf_compl_singleton_isMaximal`：idealOf_compl_singleton
_isMaximal (x : X) : (idealOfSet 𝕜 ({x}ᶜ : Set X)).IsMaximal
-/
theorem ideal_isMaximal_iff (I : Ideal C(X, 𝕜)) [hI : IsClosed (I : Set C(X, 𝕜))] :
    I.IsMaximal ↔ ∃ x : X, idealOfSet 𝕜 {x}ᶜ = I := by
  refine
    ⟨?_, fun h =>
      let ⟨x, hx⟩ := h
      hx ▸ idealOf_compl_singleton_isMaximal 𝕜 x⟩
  intro hI'
  obtain ⟨x, hx⟩ := setOfIdeal_eq_compl_singleton I
  exact
    ⟨x, by
      simpa only [idealOfSet_ofIdeal_eq_closure, I.closure_eq_of_isClosed hI] using
        congr_arg (idealOfSet 𝕜) hx.symm⟩

end RCLike

end ContinuousMap

namespace WeakDual

namespace CharacterSpace

open Function ContinuousMap

variable (X 𝕜 : Type*) [TopologicalSpace X]

section ContinuousMapEval

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
variable [Nontrivial 𝕜] [NoZeroDivisors 𝕜]

/-- The natural continuous map from a locally compact topological space `X` to the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point evaluation at `x`. -/
/-
**WeakDual.CharacterSpace.continuousMapEval** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.
CharacterSpace`。
形式化陈述：continuousMapEval : C(X, characterSpace 𝕜 C(X, 𝕜)) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural continuous map from a locally compact topological space `X` to the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point evaluation at `
x`.
-/
def continuousMapEval : C(X, characterSpace 𝕜 C(X, 𝕜)) where
  toFun x :=
    ⟨{  toFun := fun f => f x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }, by
        rw [CharacterSpace.eq_set_map_one_map_mul]; exact ⟨rfl, fun f g => rfl⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_of_continuous_eval map_continuous) _

@[simp]
/-
**WeakDual.CharacterSpace.continuousMapEval_apply_apply** 是 Mathlib 中的一个定理，位于命名空
间 `WeakDual.CharacterSpace`。
形式化陈述：continuousMapEval_apply_apply (x : X) (f : C(X, 𝕜)) : continuousMapEval X 
𝕜 x f = f x
参数：x : X；f : C(X, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
theorem continuousMapEval_apply_apply (x : X) (f : C(X, 𝕜)) : continuousMapEval X 𝕜 x f = f x :=
  rfl

end ContinuousMapEval

variable [CompactSpace X] [T2Space X] [RCLike 𝕜]

/-
**WeakDual.CharacterSpace.continuousMapEval_bijective** 是 Mathlib 中的一个定理，位于命名空间 
`WeakDual.CharacterSpace`。
形式化陈述：continuousMapEval_bijective : Bijective (continuousMapEval X 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `RCLike.continuous_ofReal`：continuous_ofReal : Continuous (ofReal : Real 
-> K)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
（共 39 条，此处仅展示前 30 条）
-/
theorem continuousMapEval_bijective : Bijective (continuousMapEval X 𝕜) := by
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · contrapose! hxy
    rcases exists_continuous_zero_one_of_isClosed (isClosed_singleton : _root_.IsClosed {x})
        (isClosed_singleton : _root_.IsClosed {y}) (Set.disjoint_singleton.mpr hxy) with
      ⟨f, fx, fy, -⟩
    rw [DFunLike.ne_iff]
    use (⟨fun (x : ℝ) => (x : 𝕜), RCLike.continuous_ofReal⟩ : C(ℝ, 𝕜)).comp f
    simpa only [continuousMapEval_apply_apply, ContinuousMap.comp_apply, coe_mk, Ne,
      RCLike.ofReal_inj] using
      ((fx (Set.mem_singleton x)).symm ▸ (fy (Set.mem_singleton y)).symm ▸ zero_ne_one : f x ≠ f y)
  · obtain ⟨x, hx⟩ := (ideal_isMaximal_iff (RingHom.ker φ)).mp inferInstance
    refine ⟨x, CharacterSpace.ext_ker <| Ideal.ext fun f => ?_⟩
    simpa only [RingHom.mem_ker, continuousMapEval_apply_apply, mem_idealOfSet_compl_singleton,
      RingHom.mem_ker] using SetLike.ext_iff.mp hx f

/-- This is the natural homeomorphism between a compact Hausdorff space `X` and the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)`. -/
/-
**WeakDual.CharacterSpace.homeoEval** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.Characte
rSpace`。
形式化陈述：homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WeakDual.CharacterSpace.continuousMapEval_bijective`：continuousMapEval_b
ijective : Bijective (continuousMapEval X 𝕜)

--- 原说明 ---
This is the natural homeomorphism between a compact Hausdorff space `X` and the
`WeakDual.characterSpace 𝕜 C(X, 𝕜)`.
-/
noncomputable def homeoEval : X ≃ₜ characterSpace 𝕜 C(X, 𝕜) :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    { Equiv.ofBijective _ (continuousMapEval_bijective X 𝕜) with toFun := continuousMapEval X 𝕜 }
    (map_continuous (continuousMapEval X 𝕜))

end CharacterSpace

end WeakDual

