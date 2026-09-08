/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Anatole Dedecker
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Linear topologies on modules and rings

Let `M` be a (left) module over a ring `R`. Following
[Stacks: Definition 15.36.1](https://stacks.math.columbia.edu/tag/07E8), we say that a
topology on `M` is *`R`-linear* if it is invariant by translations and admits a basis of
neighborhoods of 0 consisting of (left) `R`-submodules.

If `M` is an `(R, R')`-bimodule, we show that a topology is both `R`-linear and `R'`-linear
if and only if there exists a basis of neighborhoods of 0 consisting of `(R, R')`-subbimodules.

In particular, we say that a topology on the ring `R` is *linear* if it is linear if
it is linear when `R` is viewed as an `(R, Rᵐᵒᵖ)`-bimodule. By the previous results,
this means that there exists a basis of neighborhoods of 0 consisting of two-sided ideals,
hence our definition agrees with [N. Bourbaki, *Algebra II*, chapter 4, §2, n° 3][bourbaki1981].

## Main definitions and statements

* `IsLinearTopology R M`: the topology on `M` is `R`-linear, meaning that there exists a basis
  of neighborhoods of 0 consisting of `R`-submodules. Note that we don't impose that the topology
  is invariant by translation, so you'll often want to add `ContinuousConstVAdd M M` to get
  something meaningful. To express that the topology of a ring `R` is linear, use
  `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`.
* `IsLinearTopology.mk_of_hasBasis`: a convenient constructor for `IsLinearTopology`.
  See also `IsLinearTopology.mk_of_hasBasis'`.
* The discrete topology on `M` is `R`-linear (declared as an `instance`).
* `IsLinearTopology.hasBasis_subbimodule`: assume that `M` is an `(R, R')`-bimodule,
  and that its topology is both `R`-linear and `R'`-linear. Then there exists a basis of
  neighborhoods of 0 made of `(R, R')`-subbimodules. Note that this is not trivial, since the bases
  witnessing `R`-linearity and `R'`-linearity may have nothing to do with each other
* `IsLinearTopology.tendsto_smul_zero`: assume that the topology on `M` is linear.
  For `m : ι → M` such that `m i` tends to 0, `r i • m i` still tends to 0 for any `r : ι → R`.

* `IsLinearTopology.hasBasis_twoSidedIdeal`: if the ring `R` is linearly topologized,
  in the sense that we have both `IsLinearTopology R R` and `IsLinearTopology Rᵐᵒᵖ R`,
  then there exists a basis of neighborhoods of 0 consisting of two-sided ideals.
* Conversely, to prove `IsLinearTopology R R` and `IsLinearTopology Rᵐᵒᵖ R`
  from a basis of two-sided ideals, use `IsLinearTopology.mk_of_hasBasis'` twice.
* `IsLinearTopology.tendsto_mul_zero_of_left`: assume that the topology on `R` is (right-)linear.
  For `f, g : ι → R` such that `f i` tends to `0`, `f i * g i` still tends to `0`.
* `IsLinearTopology.tendsto_mul_zero_of_right`: assume that the topology on `R` is (left-)linear.
  For `f, g : ι → R` such that `g i` tends to `0`, `f i * g i` still tends to `0`
* If `R` is a commutative ring and its topology is left-linear, it is automatically
  right-linear (declared as a low-priority instance).

## Notes on the implementation

* Some statements assume `ContinuousAdd M` where `ContinuousConstVAdd M M`
  (invariance by translation) would be enough. In fact, in presence of `IsLinearTopology R M`,
  invariance by translation implies that `M` is a topological additive group on which `R` acts
  by homeomorphisms. Similarly, `IsLinearTopology R R` and `ContinuousConstVAdd R R` imply that
  `R` is a topological ring. All of this will follow from https://github.com/leanprover-community/mathlib4/issues/18437.

  Nevertheless, we don't plan on adding those facts as instances: one should use directly
  results from https://github.com/leanprover-community/mathlib4/issues/18437 to get `IsTopologicalAddGroup` and `IsTopologicalRing` instances.

* The main constructor for `IsLinearTopology`, `IsLinearTopology.mk_of_hasBasis`
  is formulated in terms of the subobject classes `AddSubmonoidClass` and `SMulMemClass`
  to allow for more complicated types than `Submodule R M` or `Ideal R`. Unfortunately, the scalar
  ring in `SMulMemClass` is an `outParam`, which means that Lean only considers one base ring for
  a given subobject type. For example, Lean will *never* find `SMulMemClass (TwoSidedIdeal R) R R`
  because it prioritizes the (later-defined) instance of `SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R`.

  This makes `IsLinearTopology.mk_of_hasBasis` un-applicable to `TwoSidedIdeal` (and probably other
  types), thus we provide `IsLinearTopology.mk_of_hasBasis'` as an alternative not relying on
  typeclass inference.
-/

public section

open scoped Topology
open Filter

namespace IsLinearTopology

section Module

variable {R R' M : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M] [Module R' M]
  [SMulCommClass R R' M] [TopologicalSpace M]

variable (R M) in
/-- Consider a (left-)module `M` over a ring `R`. A topology on `M` is *`R`-linear*
if the open sub-`R`-modules of `M` form a basis of neighborhoods of zero.

Typically one would also that the topology is invariant by translation (`ContinuousConstVAdd M M`),
or equivalently that `M` is a topological group, but we do not assume it for the definition.

In particular, we say that a topology on the ring `R` is *linear* if it is both
`R`-linear and `Rᵐᵒᵖ`-linear for the obvious module structures. To spell this in Lean,
simply use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`. -/
/-
**IsLinearTopology._root_.IsLinearTopology** 是 Mathlib 中的一个类，位于命名空间 `IsLinearTop
ology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a (left-)module `M` over a ring `R`. A topology on `M` is *`R`-linear*
if the open sub-`R`-modules of `M` form a basis of neighborhoods of zero.

Typically one would also that the topology is invariant by translation (`Continu
ousConstVAdd M M`),
or equivalently that `M` is a topological group, but we do not assume it for the
 definition.

In particular, we say that a topology on the ring `R` is *linear* if it is both
`R`-linear and `Rᵐᵒᵖ`-linear for the obvious module structures. To spell this in
 Lean,
simply use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`.
-/
class _root_.IsLinearTopology where
  hasBasis_submodule' : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M))

variable (R) in
/-
**IsLinearTopology.hasBasis_submodule** 是 Mathlib 中的一个引理，位于命名空间 `IsLinearTopolog
y`。
形式化陈述：hasBasis_submodule [IsLinearTopology R M] : (𝓝 (0 : M)).HasBasis (fun N : 
Submodule R M => (N : Set M) in 𝓝 0) (fun N : Submodule R M => (N : Set M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearTopology.hasBasis_submodule'`：∀ {R : Type u_1} {M : Type u_3} {i
nst : Ring R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   {inst_3 :
 TopologicalSpace M} [self…
-/
lemma hasBasis_submodule [IsLinearTopology R M] : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M)) :=
  IsLinearTopology.hasBasis_submodule'

variable (R) in
/-
**IsLinearTopology.hasBasis_open_submodule** 是 Mathlib 中的一个引理，位于命名空间 `IsLinearTo
pology`。
形式化陈述：hasBasis_open_submodule [ContinuousAdd M] [IsLinearTopology R M] : (𝓝 (0 :
 M)).HasBasis (fun N : Submodule R M => IsOpen (N : Set M)) (fun N : Submodule R
 M => (N : Set M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.congr`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p
 : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {p' : ι → Prop} {s' : ι →
 Set α}, (∀…
· 使用引理 `IsLinearTopology.hasBasis_submodule`：hasBasis_submodule [IsLinearTopolog
y R M] : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun
 N : Submodule R M => (N …
· 使用定理 `AddSubgroup.isOpen_of_mem_nhds`：∀ {G : Type u_1} [inst : AddGroup G] [in
st_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (H : AddSubgroup G)   {g 
: G}, ↑H ∈ nhds g → …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma hasBasis_open_submodule [ContinuousAdd M] [IsLinearTopology R M] :
    (𝓝 (0 : M)).HasBasis
      (fun N : Submodule R M ↦ IsOpen (N : Set M)) (fun N : Submodule R M ↦ (N : Set M)) :=
  hasBasis_submodule R |>.congr
    (fun N ↦ ⟨N.toAddSubgroup.isOpen_of_mem_nhds, fun hN ↦ hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ ↦ rfl)

variable (R) in
/-- A variant of `IsLinearTopology.mk_of_hasBasis` asking for an explicit proof that `S`
is a class of submodules instead of relying on (fragile) typeclass inference of `SMulCommClass`. -/
/-
**IsLinearTopology.mk_of_hasBasis'** 是 Mathlib 中的一个引理，位于命名空间 `IsLinearTopology`。
形式化陈述：mk_of_hasBasis' {ι : Sort*} {S : Type*} [SetLike S M] [AddSubmonoidClass S
 M] {p : ι -> Prop} {s : ι -> S} (h : (𝓝 0).HasBasis p (fun i => (s i : Set M)))
 (hsmul : forall s : S, forall r : R, forall m in s, r • m in s) : IsLinearTopol
ogy R M where hasBasis_submodule'
参数：h : (𝓝 0).HasBasis p (fun i => (s i : Set M))；hsmul : forall s : S, forall r 
: R, forall m in s, r • m in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)

--- 原说明 ---
A variant of `IsLinearTopology.mk_of_hasBasis` asking for an explicit proof that
 `S`
is a class of submodules instead of relying on (fragile) typeclass inference of 
`SMulCommClass`.
-/
lemma mk_of_hasBasis' {ι : Sort*} {S : Type*} [SetLike S M]
    [AddSubmonoidClass S M]
    {p : ι → Prop} {s : ι → S}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set M)))
    (hsmul : ∀ s : S, ∀ r : R, ∀ m ∈ s, r • m ∈ s) :
    IsLinearTopology R M where
  hasBasis_submodule' := h.to_hasBasis
    (fun i hi ↦ ⟨
      { carrier := s i,
        add_mem' := add_mem,
        zero_mem' := zero_mem _,
        smul_mem' := hsmul _},
      h.mem_of_mem hi, subset_rfl⟩)
    (fun _ ↦ h.mem_iff.mp)

variable (R) in
/-- To show that `M` is linearly-topologized as an `R`-module, it suffices to show
that it has a basis of neighborhoods of zero made of `R`-submodules.

Note: for technical reasons detailed in the module docstring, Lean sometimes struggles to find the
right `SMulMemClass` instance. See `IsLinearTopology.mk_of_hasBasis'` for a more
explicit variant. -/
/-
**IsLinearTopology.mk_of_hasBasis** 是 Mathlib 中的一个引理，位于命名空间 `IsLinearTopology`。
形式化陈述：mk_of_hasBasis {ι : Sort*} {S : Type*} [SetLike S M] [SMulMemClass S R M] 
[AddSubmonoidClass S M] {p : ι -> Prop} {s : ι -> S} (h : (𝓝 0).HasBasis p (fun 
i => (s i : Set M))) : IsLinearTopology R M
参数：h : (𝓝 0).HasBasis p (fun i => (s i : Set M))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLinearTopology.mk_of_hasBasis'`：mk_of_hasBasis' {ι : Sort*} {S : Type*
} [SetLike S M] [AddSubmonoidClass S M] {p : ι -> Prop} {s : ι -> S} (h : (𝓝 0).
HasBasis p (fun i => (…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …

--- 原说明 ---
To show that `M` is linearly-topologized as an `R`-module, it suffices to show
that it has a basis of neighborhoods of zero made of `R`-submodules.

Note: for technical reasons detailed in the module docstring, Lean sometimes str
uggles to find the
right `SMulMemClass` instance. See `IsLinearTopology.mk_of_hasBasis'` for a more
explicit variant.
-/
lemma mk_of_hasBasis {ι : Sort*} {S : Type*} [SetLike S M]
    [SMulMemClass S R M] [AddSubmonoidClass S M]
    {p : ι → Prop} {s : ι → S}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set M))) :
    IsLinearTopology R M :=
  mk_of_hasBasis' R h fun _ ↦ SMulMemClass.smul_mem
/-
**IsLinearTopology._root_.isLinearTopology_iff_hasBasis_submodule** 是 Mathlib 中的
一个定理，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLinearTopology_iff_hasBasis_submodule :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M)) :=
  ⟨fun _ ↦ hasBasis_submodule R, fun h ↦ .mk_of_hasBasis R h⟩
/-
**IsLinearTopology._root_.isLinearTopology_iff_hasBasis_open_submodule** 是 Mathl
ib 中的一个定理，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLinearTopology_iff_hasBasis_open_submodule [ContinuousAdd M] :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M ↦ IsOpen (N : Set M)) (fun N : Submodule R M ↦ (N : Set M)) :=
  ⟨fun _ ↦ hasBasis_open_submodule R, fun h ↦ .mk_of_hasBasis R h⟩

/-- The discrete topology on any `R`-module is `R`-linear. -/
/-
**IsLinearTopology.** 是 Mathlib 中的一个实例，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete topology on any `R`-module is `R`-linear.
-/
instance [DiscreteTopology M] : IsLinearTopology R M :=
  have : HasBasis (𝓝 0 : Filter M) (fun _ ↦ True) (fun (_ : Unit) ↦ (⊥ : Submodule R M)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  mk_of_hasBasis R this

variable (R R') in
open Set Pointwise in
/-- Assume that `M` is a module over two rings `R` and `R'`, and that its topology
is linear with respect to each of these rings. Then, it has a basis of neighborhoods of zero
made of sub-`(R, R')`-bimodules.

The proof is inspired by lemma 9 in [I. Kaplansky, *Topological Rings*](kaplansky_topological_1947).
TODO: Formalize the lemma in its full strength.

Note: due to the lack of a satisfying theory of sub-bimodules, we use `AddSubgroup`s with
extra conditions. -/
/-
**IsLinearTopology.hasBasis_subbimodule** 是 Mathlib 中的一个引理，位于命名空间 `IsLinearTopol
ogy`。
形式化陈述：hasBasis_subbimodule [IsLinearTopology R M] [IsLinearTopology R' M] : (𝓝 (
0 : M)).HasBasis (fun I : AddSubgroup M => (I : Set M) in 𝓝 0 ∧ (forall r : R, f
orall x in I, r • x in I) ∧ (forall r' : R', forall x in I, r' • x in I)) (fun I
 : AddSubgroup M => (I : Set M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用引理 `IsLinearTopology.hasBasis_submodule`：hasBasis_submodule [IsLinearTopolog
y R M] : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun
 N : Submodule R M => (N …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.smul_subset_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {
s : Set α} {t u : Set β}, s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Set.smul_subset_smul_left`：smul_subset_smul_left : t₁ subseteq t₂ -> s •
 t₁ subseteq s • t₂
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : S
et α} {t₁ t₂ : Set β}, s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Set.smul_subset_smul`：smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t
₂ -> s₁ • t₁ subseteq s₂ • t₂
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `AddSubgroup.closure_induction`：∀ {G : Type u_1} [inst : AddGroup G] {k :
 Set G} {p : (g : G) → g ∈ AddSubgroup.closure k → Prop},   (∀ (x : G) (hx : x ∈
 k), p x ⋯) →     p…
· 使用定理 `AddSubgroup.subset_closure`：∀ {G : Type u_1} [inst : AddGroup G] {k : Se
t G}, k ⊆ ↑(AddSubgroup.closure k)
· 使用定理 `Set.smul_mem_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
: Set α} {t : Set β} {a : α} {b : β}, a ∈ s → b ∈ t → a • b ∈ s • t
· 使用定理 `trivial`：True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Assume that `M` is a module over two rings `R` and `R'`, and that its topology
is linear with respect to each of these rings. Then, it has a basis of neighborh
oods of zero
made of sub-`(R, R')`-bimodules.

The proof is inspired by lemma 9 in [I. Kaplansky, *Topological Rings*](kaplansk
y_topological_1947).
TODO: Formalize the lemma in its full strength.

Note: due to the lack of a satisfying theory of sub-bimodules, we use `AddSubgro
up`s with
extra conditions.
-/
lemma hasBasis_subbimodule [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M ↦ (I : Set M) ∈ 𝓝 0 ∧
        (∀ r : R, ∀ x ∈ I, r • x ∈ I) ∧ (∀ r' : R', ∀ x ∈ I, r' • x ∈ I))
      (fun I : AddSubgroup M ↦ (I : Set M)) := by
  -- Start from a neighborhood `V`. It contains some open sub-`R`-module `I`.
  refine IsLinearTopology.hasBasis_submodule R |>.to_hasBasis (fun I hI ↦ ?_)
    (fun I hI ↦ ⟨{I with smul_mem' := fun r x hx ↦ hI.2.1 r x hx}, hI.1, subset_rfl⟩)
  -- `I` itself is a neighborhood of zero, so it contains some open sub-`R'`-module `J`.
  rcases (hasBasis_submodule R').mem_iff.mp hI with ⟨J, hJ, J_sub_I⟩
  set uR : Set R := univ -- Convenient to avoid type ascriptions
  set uR' : Set R' := univ
  have hRR : uR * uR ⊆ uR := subset_univ _
  have hRI : uR • (I : Set M) ⊆ I := smul_subset_iff.mpr fun x _ i hi ↦ I.smul_mem x hi
  have hR'J : uR' • (J : Set M) ⊆ J := smul_subset_iff.mpr fun x _ j hj ↦ J.smul_mem x hj
  have hRJ : uR • (J : Set M) ⊆ I := subset_trans (smul_subset_smul_left J_sub_I) hRI
  -- Note that, on top of the obvious `R • I ⊆ I` and `R' • J ⊆ J`, we have `R • J ⊆ R • I ⊆ I`.
  -- Now set `S := J ∪ (R • J)`. We have:
  -- 1. `R • S = (R • J) ∪ (R • R • J) ⊆ R • J ⊆ S`.
  -- 2. `R' • S = (R' • J) ∪ (R' • R • J) ⊆ J ∪ (R • R' • J) ⊆ J ∪ (R • J) = S`.
  -- Hence the subgroup `A` generated by `S` is a sub-`(R, R')`-bimodule,
  -- which we claim is open and contained in `I`.
  -- Indeed, we have `J ⊆ S ⊆ I`, hence `J ⊆ A ⊆ I`, and `J` is open by hypothesis.
  set S : Set M := J ∪ uR • J
  have S_sub_I : S ⊆ I := union_subset J_sub_I hRJ
  have hRS : uR • S ⊆ S := calc
    uR • S = uR • (J : Set M) ∪ (uR * uR) • (J : Set M) := by simp_rw [S, smul_union, mul_smul]
    _ ⊆ uR • (J : Set M) ∪ uR • (J : Set M) := by gcongr
    _ = uR • (J : Set M) := union_self _
    _ ⊆ S := subset_union_right
  have hR'S : uR' • S ⊆ S := calc
    uR' • S = uR' • (J : Set M) ∪ uR • uR' • (J : Set M) := by simp_rw [S, smul_union, smul_comm]
    _ ⊆ J ∪ uR • J := by gcongr
    _ = S := rfl
  set A : AddSubgroup M := .closure S
  have hRA : ∀ r : R, ∀ i ∈ A, r • i ∈ A := fun r i hi ↦ by
    refine AddSubgroup.closure_induction (fun x hx => ?base) ?zero (fun x y _ _ hx hy ↦ ?add)
      (fun x _ hx ↦ ?neg) hi
    case base => exact AddSubgroup.subset_closure <| hRS <| Set.smul_mem_smul trivial hx
    case zero => simp_rw [smul_zero]; exact zero_mem _
    case add => simp_rw [smul_add]; exact add_mem hx hy
    case neg => simp_rw [smul_neg]; exact neg_mem hx
  have hR'A : ∀ r' : R', ∀ i ∈ A, r' • i ∈ A := fun r' i hi ↦ by
    refine AddSubgroup.closure_induction (fun x hx => ?base) ?zero (fun x y _ _ hx hy ↦ ?add)
      (fun x _ hx ↦ ?neg) hi
    case base => exact AddSubgroup.subset_closure <| hR'S <| Set.smul_mem_smul trivial hx
    case zero => simp_rw [smul_zero]; exact zero_mem _
    case add => simp_rw [smul_add]; exact add_mem hx hy
    case neg => simp_rw [smul_neg]; exact neg_mem hx
  have A_sub_I : (A : Set M) ⊆ I := I.toAddSubgroup.closure_le.mpr S_sub_I
  have J_sub_A : (J : Set M) ⊆ A := subset_trans subset_union_left AddSubgroup.subset_closure
  exact ⟨A, ⟨mem_of_superset hJ J_sub_A, hRA, hR'A⟩, A_sub_I⟩

variable (R R') in
open Set Pointwise in
/-- A variant of `IsLinearTopology.hasBasis_subbimodule` using `IsOpen I` instead of `I ∈ 𝓝 0`. -/
/-
**IsLinearTopology.hasBasis_open_subbimodule** 是 Mathlib 中的一个引理，位于命名空间 `IsLinear
Topology`。
形式化陈述：hasBasis_open_subbimodule [ContinuousAdd M] [IsLinearTopology R M] [IsLine
arTopology R' M] : (𝓝 (0 : M)).HasBasis (fun I : AddSubgroup M => IsOpen (I : Se
t M) ∧ (forall r : R, forall x in I, r • x in I) ∧ (forall r' : R', forall x in 
I, r' • x in I)) (fun I : AddSubgroup M => (I : Set M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.congr`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p
 : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {p' : ι → Prop} {s' : ι →
 Set α}, (∀…
· 使用引理 `IsLinearTopology.hasBasis_subbimodule`：hasBasis_subbimodule [IsLinearTop
ology R M] [IsLinearTopology R' M] : (𝓝 (0 : M)).HasBasis (fun I : AddSubgroup M
 => (I : Set M) in 𝓝 0 ∧ (f…
· 使用定理 `and_congr_left'`：∀ {a b c : Prop}, (a ↔ b) → (a ∧ c ↔ b ∧ c)
· 使用定理 `AddSubgroup.isOpen_of_mem_nhds`：∀ {G : Type u_1} [inst : AddGroup G] [in
st_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (H : AddSubgroup G)   {g 
: G}, ↑H ∈ nhds g → …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G

--- 原说明 ---
A variant of `IsLinearTopology.hasBasis_subbimodule` using `IsOpen I` instead of
 `I ∈ 𝓝 0`.
-/
lemma hasBasis_open_subbimodule [ContinuousAdd M] [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M ↦ IsOpen (I : Set M) ∧
        (∀ r : R, ∀ x ∈ I, r • x ∈ I) ∧ (∀ r' : R', ∀ x ∈ I, r' • x ∈ I))
      (fun I : AddSubgroup M ↦ (I : Set M)) :=
  hasBasis_subbimodule R R' |>.congr
    (fun N ↦ and_congr_left' ⟨N.isOpen_of_mem_nhds, fun hN ↦ hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ ↦ rfl)

-- Even though `R` can be recovered from `a`, the nature of this lemma means that `a` will
-- often be left for Lean to infer, so making `R` explicit is useful in practice.
variable (R) in
/-- If `M` is a linearly topologized `R`-module and `i ↦ m i` tends to zero,
then `i ↦ a i • m i` still tends to zero for any family `a : ι → R`. -/
/-
**IsLinearTopology.tendsto_smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearTopology
`。
形式化陈述：tendsto_smul_zero [IsLinearTopology R M] {ι : Type*} {f : Filter ι} (a : ι
 -> R) (m : ι -> M) (ha : Tendsto m f (𝓝 0)) : Tendsto (a • m) f (𝓝 0)
参数：a : ι -> R；m : ι -> M；ha : Tendsto m f (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用引理 `IsLinearTopology.hasBasis_submodule`：hasBasis_submodule [IsLinearTopolog
y R M] : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun
 N : Submodule R M => (N …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p

--- 原说明 ---
If `M` is a linearly topologized `R`-module and `i ↦ m i` tends to zero,
then `i ↦ a i • m i` still tends to zero for any family `a : ι → R`.
-/
theorem tendsto_smul_zero [IsLinearTopology R M] {ι : Type*} {f : Filter ι}
    (a : ι → R) (m : ι → M) (ha : Tendsto m f (𝓝 0)) :
    Tendsto (a • m) f (𝓝 0) := by
  rw [hasBasis_submodule R |>.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.smul_mem _ ai_mem

variable (R) in
/-- If the left and right actions of `R` on `M` coincide, then a topology is `Rᵐᵒᵖ`-linear
if and only if it is `R`-linear. -/
/-
**IsLinearTopology._root_.IsCentralScalar.isLinearTopology_iff** 是 Mathlib 中的一个定
理，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the left and right actions of `R` on `M` coincide, then a topology is `Rᵐᵒᵖ`-
linear
if and only if it is `R`-linear.
-/
theorem _root_.IsCentralScalar.isLinearTopology_iff [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsLinearTopology Rᵐᵒᵖ M ↔ IsLinearTopology R M := by
  constructor <;> intro H
  · exact mk_of_hasBasis' R (IsLinearTopology.hasBasis_submodule Rᵐᵒᵖ)
      fun S r m hm ↦ op_smul_eq_smul r m ▸ S.smul_mem _ hm
  · exact mk_of_hasBasis' Rᵐᵒᵖ (IsLinearTopology.hasBasis_submodule R)
      fun S r m hm ↦ unop_smul_eq_smul r m ▸ S.smul_mem _ hm

end Module

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-
**IsLinearTopology.hasBasis_ideal** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearTopology`。
形式化陈述：hasBasis_ideal [IsLinearTopology R R] : (𝓝 0).HasBasis (fun I : Ideal R =>
 (I : Set R) in 𝓝 0) (fun I : Ideal R => (I : Set R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLinearTopology.hasBasis_submodule`：hasBasis_submodule [IsLinearTopolog
y R M] : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun
 N : Submodule R M => (N …
-/
theorem hasBasis_ideal [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_submodule R
/-
**IsLinearTopology.hasBasis_open_ideal** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearTopolo
gy`。
形式化陈述：hasBasis_open_ideal [ContinuousAdd R] [IsLinearTopology R R] : (𝓝 0).HasBa
sis (fun I : Ideal R => IsOpen (I : Set R)) (fun I : Ideal R => (I : Set R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLinearTopology.hasBasis_open_submodule`：hasBasis_open_submodule [Conti
nuousAdd M] [IsLinearTopology R M] : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M
 => IsOpen (N : Set M)) (fun N…
-/
theorem hasBasis_open_ideal [ContinuousAdd R] [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_open_submodule R
/-
**IsLinearTopology._root_.isLinearTopology_iff_hasBasis_ideal** 是 Mathlib 中的一个定理
，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLinearTopology_iff_hasBasis_ideal :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  isLinearTopology_iff_hasBasis_submodule
/-
**IsLinearTopology._root_.isLinearTopology_iff_hasBasis_open_ideal** 是 Mathlib 中
的一个定理，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLinearTopology_iff_hasBasis_open_ideal [IsTopologicalRing R] :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  isLinearTopology_iff_hasBasis_open_submodule
/-
**IsLinearTopology.hasBasis_right_ideal** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearTopol
ogy`。
形式化陈述：hasBasis_right_ideal [IsLinearTopology Rᵐᵒᵖ R] : (𝓝 0).HasBasis (fun I : S
ubmodule Rᵐᵒᵖ R => (I : Set R) in 𝓝 0) (fun I => (I : Set R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLinearTopology.hasBasis_submodule`：hasBasis_submodule [IsLinearTopolog
y R M] : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun
 N : Submodule R M => (N …
-/
theorem hasBasis_right_ideal [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 0).HasBasis (fun I : Submodule Rᵐᵒᵖ R ↦ (I : Set R) ∈ 𝓝 0) (fun I ↦ (I : Set R)) :=
  hasBasis_submodule Rᵐᵒᵖ

set_option backward.isDefEq.respectTransparency false in
open Set Pointwise in
/-- If a ring `R` is linearly ordered as a left *and* right module over itself,
then it has a basis of neighborhoods of zero made of *two-sided* ideals.

This is usually called a *linearly topologized ring*, but we do not add a specific spelling:
you should use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]` instead. -/
/-
**IsLinearTopology.hasBasis_twoSidedIdeal** 是 Mathlib 中的一个引理，位于命名空间 `IsLinearTop
ology`。
形式化陈述：hasBasis_twoSidedIdeal [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] : 
(𝓝 (0 : R)).HasBasis (fun I : TwoSidedIdeal R => (I : Set R) in 𝓝 0) (fun I : Tw
oSidedIdeal R => (I : Set R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用引理 `IsLinearTopology.hasBasis_subbimodule`：hasBasis_subbimodule [IsLinearTop
ology R M] [IsLinearTopology R' M] : (𝓝 (0 : M)).HasBasis (fun I : AddSubgroup M
 => (I : Set M) in 𝓝 0 ∧ (f…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.coe_mk'`：coe_mk' (carrier : Set R) (zero_mem add_mem neg_m
em mul_mem_left mul_mem_right) : (mk' carrier zero_mem add_mem neg_mem mul_mem_l
eft mul_mem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TwoSidedIdeal.mul_mem_left`：mul_mem_left (x y) (hy : y in I) : x * y in 
I
· 使用引理 `TwoSidedIdeal.mul_mem_right`：mul_mem_right (x y) (hx : x in I) : x * y i
n I
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
If a ring `R` is linearly ordered as a left *and* right module over itself,
then it has a basis of neighborhoods of zero made of *two-sided* ideals.

This is usually called a *linearly topologized ring*, but we do not add a specif
ic spelling:
you should use `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]` instead.
-/
lemma hasBasis_twoSidedIdeal [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0)
      (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_subbimodule R Rᵐᵒᵖ |>.to_hasBasis
    (fun I ⟨hI, hRI, hRI'⟩ ↦ ⟨.mk' I (zero_mem _) add_mem neg_mem (hRI _ _) (hRI' _ _),
      by simpa using hI, by simp⟩)
    (fun I hI ↦ ⟨I.asIdeal.toAddSubgroup,
      ⟨hI, I.mul_mem_left, fun r x hx ↦ I.mul_mem_right x (r.unop) hx⟩, subset_rfl⟩)
/-
**IsLinearTopology.hasBasis_open_twoSidedIdeal** 是 Mathlib 中的一个引理，位于命名空间 `IsLine
arTopology`。
形式化陈述：hasBasis_open_twoSidedIdeal [ContinuousAdd R] [IsLinearTopology R R] [IsLi
nearTopology Rᵐᵒᵖ R] : (𝓝 (0 : R)).HasBasis (fun I : TwoSidedIdeal R => IsOpen (
I : Set R)) (fun I : TwoSidedIdeal R => (I : Set R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.congr`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p
 : ι → Prop} {s : ι → Set α},   l.HasBasis p s →     ∀ {p' : ι → Prop} {s' : ι →
 Set α}, (∀…
· 使用引理 `IsLinearTopology.hasBasis_twoSidedIdeal`：hasBasis_twoSidedIdeal [IsLinea
rTopology R R] [IsLinearTopology Rᵐᵒᵖ R] : (𝓝 (0 : R)).HasBasis (fun I : TwoSide
dIdeal R => (I : Set R) in 𝓝 …
· 使用定理 `AddSubgroup.isOpen_of_mem_nhds`：∀ {G : Type u_1} [inst : AddGroup G] [in
st_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (H : AddSubgroup G)   {g 
: G}, ↑H ∈ nhds g → …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TwoSidedIdeal.instAddSubgroupClass`：∀ {R : Type u_1} [inst : NonUnitalNo
nAssocRing R], AddSubgroupClass (TwoSidedIdeal R) R
-/
lemma hasBasis_open_twoSidedIdeal [ContinuousAdd R]
    [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_twoSidedIdeal.congr
    (fun I ↦ ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)
/-
**IsLinearTopology._root_.isLinearTopology_iff_hasBasis_twoSidedIdeal** 是 Mathli
b 中的一个定理，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔
      (𝓝 0).HasBasis
        (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun ⟨_, _⟩ ↦ hasBasis_twoSidedIdeal, fun h ↦
    ⟨.mk_of_hasBasis' R h fun I r x hx ↦ I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx ↦ I.mul_mem_right x r.unop hx⟩⟩
/-
**IsLinearTopology._root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal** 是 M
athlib 中的一个定理，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal [ContinuousAdd R] :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun ⟨_, _⟩ ↦ hasBasis_open_twoSidedIdeal, fun h ↦
    ⟨.mk_of_hasBasis' R h fun I r x hx ↦ I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx ↦ I.mul_mem_right x r.unop hx⟩⟩
/-
**IsLinearTopology.tendsto_mul_zero_of_left** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearT
opology`。
形式化陈述：tendsto_mul_zero_of_left [IsLinearTopology Rᵐᵒᵖ R] {ι : Type*} {f : Filter
 ι} (a b : ι -> R) (ha : Tendsto a f (𝓝 0)) : Tendsto (a * b) f (𝓝 0)
参数：a b : ι -> R；ha : Tendsto a f (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearTopology.tendsto_smul_zero`：tendsto_smul_zero [IsLinearTopology 
R M] {ι : Type*} {f : Filter ι} (a : ι -> R) (m : ι -> M) (ha : Tendsto m f (𝓝 0
)) : Tendsto (a • m) f (…
-/
theorem tendsto_mul_zero_of_left [IsLinearTopology Rᵐᵒᵖ R] {ι : Type*} {f : Filter ι}
    (a b : ι → R) (ha : Tendsto a f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) :=
  tendsto_smul_zero (R := Rᵐᵒᵖ) _ _ ha
/-
**IsLinearTopology.tendsto_mul_zero_of_right** 是 Mathlib 中的一个定理，位于命名空间 `IsLinear
Topology`。
形式化陈述：tendsto_mul_zero_of_right [IsLinearTopology R R] {ι : Type*} {f : Filter ι
} (a b : ι -> R) (hb : Tendsto b f (𝓝 0)) : Tendsto (a * b) f (𝓝 0)
参数：a b : ι -> R；hb : Tendsto b f (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearTopology.tendsto_smul_zero`：tendsto_smul_zero [IsLinearTopology 
R M] {ι : Type*} {f : Filter ι} (a : ι -> R) (m : ι -> M) (ha : Tendsto m f (𝓝 0
)) : Tendsto (a • m) f (…
-/
theorem tendsto_mul_zero_of_right [IsLinearTopology R R] {ι : Type*} {f : Filter ι}
    (a b : ι → R) (hb : Tendsto b f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) :=
  tendsto_smul_zero (R := R) _ _ hb

end Ring

section CommRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R]

/-- If `R` is commutative and left-linearly topologized, it is also right-linearly topologized. -/
/-
**IsLinearTopology.** 是 Mathlib 中的一个实例，位于命名空间 `IsLinearTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is commutative and left-linearly topologized, it is also right-linearly t
opologized.
-/
instance (priority := 100) [IsLinearTopology R R] :
    IsLinearTopology Rᵐᵒᵖ R := by
  rwa [IsCentralScalar.isLinearTopology_iff]

end CommRing

end IsLinearTopology

