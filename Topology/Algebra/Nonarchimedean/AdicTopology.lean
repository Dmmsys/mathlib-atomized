/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.UniformSpace.Equiv

import Mathlib.Topology.Algebra.UniformRing  -- shake: keep (used in `example` only)

/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `IsAdic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `WithIdeal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `Ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `Ideal.adicTopology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `Ideal.nonarchimedean`: the adic topology is non-archimedean
* `isAdic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `WithIdeal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as an `R`-module.

-/

@[expose] public section


variable {R : Type*} [CommRing R]

open Set IsTopologicalAddGroup Submodule Filter

open Topology Pointwise

namespace Ideal

/-
**Ideal.adic_basis** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : Nat => (I ^ n • ⊤ :
 Ideal R)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Ideal.map_id`：map_id : I.map (RingHom.id R) = I
-/
theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : ℕ => (I ^ n • ⊤ : Ideal R) :=
  { inter := by
      suffices ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j by
        simpa only [smul_eq_mul, mul_top, Algebra.algebraMap_self, map_id, le_inf_iff] using! this
      intro i j
      exact ⟨max i j, pow_le_pow_right (le_max_left i j), pow_le_pow_right (le_max_right i j)⟩
    leftMul := by
      suffices ∀ (a : R) (i : ℕ), ∃ j : ℕ, a • I ^ j ≤ I ^ i by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro r n
      use n
      rintro a ⟨x, hx, rfl⟩
      exact (I ^ n).smul_mem r hx
    mul := by
      suffices ∀ i : ℕ, ∃ j : ℕ, (↑(I ^ j) * ↑(I ^ j) : Set R) ⊆ (↑(I ^ i) : Set R) by
        simpa only [smul_top_eq_map, Algebra.algebraMap_self, map_id] using! this
      intro n
      use n
      rintro a ⟨x, _hx, b, hb, rfl⟩
      exact (I ^ n).smul_mem x hb }

/-- The adic ring filter basis associated to an ideal `I` is made of powers of `I`. -/
@[instance_reducible]
/-
**Ideal.ringFilterBasis** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：ringFilterBasis (I : Ideal R)
参数：I : Ideal R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The adic ring filter basis associated to an ideal `I` is made of powers of `I`.
-/
def ringFilterBasis (I : Ideal R) :=
  I.adic_basis.toRing_subgroups_basis.toRingFilterBasis

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
@[instance_reducible]
/-
**Ideal.adicTopology** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：adicTopology (I : Ideal R) : TopologicalSpace R
参数：I : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ideal.adic_basis`：adic_basis (I : Ideal R) : SubmodulesRingBasis fun n :
 Nat => (I ^ n • ⊤ : Ideal R)

--- 原说明 ---
The adic topology associated to an ideal `I`. This topology admits powers of `I`
 as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archi
medean.
-/
def adicTopology (I : Ideal R) : TopologicalSpace R :=
  (adic_basis I).topology
/-
**Ideal.nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adicTopology
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingSubgroupsBasis.nonarchimedean`：nonarchimedean : @NonarchimedeanRing 
A _ hB.topology
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SubmodulesRingBasis.toRing_subgroups_basis`：toRing_subgroups_basis (hB :
 SubmodulesRingBasis B) : RingSubgroupsBasis fun i => (B i).toAddSubgroup
· 使用定理 `Ideal.adic_basis`：adic_basis (I : Ideal R) : SubmodulesRingBasis fun n :
 Nat => (I ^ n • ⊤ : Ideal R)
-/
theorem nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adicTopology :=
  I.adic_basis.toRing_subgroups_basis.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
/-
**Ideal.hasBasis_nhds_zero_adic** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：hasBasis_nhds_zero_adic (I : Ideal R) : HasBasis (@nhds R I.adicTopology (
0 : R)) (fun _n : Nat => True) fun n => ((I ^ n : Ideal R) : Set R)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `AddGroupFilterBasis.nhds_zero_hasBasis`：∀ {G : Type u} [inst : AddGroup 
G] (B : AddGroupFilterBasis G), (nhds 0).HasBasis (fun V => V ∈ B) id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For the `I`-adic topology, the neighborhoods of zero has basis given by the powe
rs of `I`.
-/
theorem hasBasis_nhds_zero_adic (I : Ideal R) :
    HasBasis (@nhds R I.adicTopology (0 : R)) (fun _n : ℕ => True) fun n =>
      ((I ^ n : Ideal R) : Set R) :=
  ⟨by
    intro U
    rw [I.ringFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, h⟩
      replace h : ↑(I ^ i) ⊆ U := by simpa using h
      exact ⟨i, trivial, h⟩
    · rintro ⟨i, -, h⟩
      exact ⟨(I ^ i : Ideal R), ⟨i, by simp⟩, h⟩⟩
/-
**Ideal.hasBasis_nhds_adic** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：hasBasis_nhds_adic (I : Ideal R) (x : R) : HasBasis (@nhds R I.adicTopolog
y x) (fun _n : Nat => True) fun n => (fun y => x + y) '' (I ^ n : Ideal R)
参数：I : Ideal R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Ideal.hasBasis_nhds_zero_adic`：hasBasis_nhds_zero_adic (I : Ideal R) : H
asBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n => ((I ^ n
 : Ideal R) : Set R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SubmodulesRingBasis.toRing_subgroups_basis`：toRing_subgroups_basis (hB :
 SubmodulesRingBasis B) : RingSubgroupsBasis fun i => (B i).toAddSubgroup
· 使用定理 `Ideal.adic_basis`：adic_basis (I : Ideal R) : SubmodulesRingBasis fun n :
 Nat => (I ^ n • ⊤ : Ideal R)
-/
theorem hasBasis_nhds_adic (I : Ideal R) (x : R) :
    HasBasis (@nhds R I.adicTopology x) (fun _n : ℕ => True) fun n =>
      (fun y => x + y) '' (I ^ n : Ideal R) := by
  let := I.adicTopology
  have := I.hasBasis_nhds_zero_adic.map fun y => x + y
  rwa [map_add_left_nhds_zero x] at this
/-
**Ideal.isLinearTopology** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isLinearTopology (I : Ideal R) : @IsLinearTopology R R _ _ _ I.adicTopolog
y
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLinearTopology.mk_of_hasBasis`：mk_of_hasBasis {ι : Sort*} {S : Type*} 
[SetLike S M] [SMulMemClass S R M] [AddSubmonoidClass S M] {p : ι -> Prop} {s : 
ι -> S} (h : (𝓝 0).Ha…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.hasBasis_nhds_zero_adic`：hasBasis_nhds_zero_adic (I : Ideal R) : H
asBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n => ((I ^ n
 : Ideal R) : Set R…
-/
theorem isLinearTopology (I : Ideal R) : @IsLinearTopology R R _ _ _ I.adicTopology :=
  letI := I.adicTopology
  IsLinearTopology.mk_of_hasBasis _ I.hasBasis_nhds_zero_adic

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
/-
**Ideal.adic_module_basis** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：adic_module_basis : I.ringFilterBasis.SubmodulesBasis fun n : Nat => I ^ n
 • (⊤ : Submodule R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
-/
theorem adic_module_basis :
    I.ringFilterBasis.SubmodulesBasis fun n : ℕ => I ^ n • (⊤ : Submodule R M) :=
  { inter := fun i j =>
      ⟨max i j,
        le_inf_iff.mpr
          ⟨smul_mono_left <| pow_le_pow_right (le_max_left i j),
            smul_mono_left <| pow_le_pow_right (le_max_right i j)⟩⟩
    smul := fun m i =>
      ⟨(I ^ i • ⊤ : Ideal R), ⟨i, by simp⟩, fun a a_in => by
        replace a_in : a ∈ I ^ i := by simpa [(I ^ i).mul_top] using a_in
        exact smul_mem_smul a_in mem_top⟩ }

/-- The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
@[instance_reducible]
/-
**Ideal.adicModuleTopology** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：adicModuleTopology : TopologicalSpace M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ideal.adic_basis`：adic_basis (I : Ideal R) : SubmodulesRingBasis fun n :
 Nat => (I ^ n • ⊤ : Ideal R)
· 使用定理 `Ideal.adic_module_basis`：adic_module_basis : I.ringFilterBasis.Submodule
sBasis fun n : Nat => I ^ n • (⊤ : Submodule R M)

--- 原说明 ---
The topology on an `R`-module `M` associated to an ideal `M`. Submodules $I^n M$
,
written `I^n • ⊤` form a basis of neighborhoods of zero.
-/
def adicModuleTopology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M))

/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on an `R`-module `M`, seen as open additive subgroups of `M`. -/
/-
**Ideal.openAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：openAddSubgroup (n : Nat) : @OpenAddSubgroup R _ I.adicTopology
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elements of the basis of neighborhoods of zero for the `I`-adic topology
on an `R`-module `M`, seen as open additive subgroups of `M`.
-/
def openAddSubgroup (n : ℕ) : @OpenAddSubgroup R _ I.adicTopology := by
  letI := I.adicTopology
  refine ⟨(I ^ n).toAddSubgroup, ?_⟩
  convert! (I.adic_basis.toRing_subgroups_basis.openAddSubgroup n).isOpen
  change (↑(I ^ n) : Set R) = ↑(I ^ n • (⊤ : Ideal R))
  simp

end Ideal

section IsAdic

/-- Given a topology on a ring `R` and an ideal `J`, `IsAdic J` means the topology is the
`J`-adic one. -/
/-
**IsAdic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop
参数：J : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a topology on a ring `R` and an ideal `J`, `IsAdic J` means the topology i
s the
`J`-adic one.
-/
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adicTopology

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
/-
**isAdic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAdic_iff [top : TopologicalSpace R] [IsTopologicalRing R] {J : Ideal R} 
: IsAdic J ↔ (forall n : Nat, IsOpen ((J ^ n : Ideal R) : Set R)) ∧ forall s in 
𝓝 (0 : R), exists n : Nat, ((J ^ n : Ideal R) : Set R) subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenAddSubgroup.isOpen'`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] (self : OpenAddSubgroup G), IsOpen (↑self).carrier
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Ideal.hasBasis_nhds_zero_adic`：hasBasis_nhds_zero_adic (I : Ideal R) : H
asBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n => ((I ^ n
 : Ideal R) : Set R…
· 使用定理 `IsTopologicalAddGroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {t t' : 
TopologicalSpace G},   IsTopologicalAddGroup G → IsTopologicalAddGroup G → nhds 
0 = nhds 0 → t …
· 使用定理 `IsTopologicalRing.to_topologicalAddGroup`：IsTopologicalRing.to_topologic
alAddGroup [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] 
: IsTopologicalAddGroup R
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SubmodulesRingBasis.toRing_subgroups_basis`：toRing_subgroups_basis (hB :
 SubmodulesRingBasis B) : RingSubgroupsBasis fun i => (B i).toAddSubgroup
· 使用定理 `Ideal.adic_basis`：adic_basis (I : Ideal R) : SubmodulesRingBasis fun n :
 Nat => (I ^ n • ⊤ : Ideal R)
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `trivial`：True
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I

--- 原说明 ---
A topological ring is `J`-adic if and only if it admits the powers of `J` as a b
asis of
open neighborhoods of zero.
-/
theorem isAdic_iff [top : TopologicalSpace R] [IsTopologicalRing R] {J : Ideal R} :
    IsAdic J ↔
      (∀ n : ℕ, IsOpen ((J ^ n : Ideal R) : Set R)) ∧
        ∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J ^ n : Ideal R) : Set R) ⊆ s := by
  constructor
  · intro H
    change _ = _ at H
    rw [H]
    let := J.adicTopology
    constructor
    · intro n
      exact (J.openAddSubgroup n).isOpen'
    · intro s hs
      simpa using J.hasBasis_nhds_zero_adic.mem_iff.mp hs
  · rintro ⟨H₁, H₂⟩
    apply IsTopologicalAddGroup.ext
    · apply @IsTopologicalRing.to_topologicalAddGroup
    · apply (RingSubgroupsBasis.toRingFilterBasis _).toAddGroupFilterBasis.isTopologicalAddGroup
    · ext s
      let := Ideal.adic_basis J
      rw [J.hasBasis_nhds_zero_adic.mem_iff]
      constructor <;> intro H
      · rcases H₂ s H with ⟨n, h⟩
        exact ⟨n, trivial, h⟩
      · rcases H with ⟨n, -, hn⟩
        rw [mem_nhds_iff]
        exact ⟨_, hn, H₁ n, (J ^ n).zero_mem⟩

variable [TopologicalSpace R] [IsTopologicalRing R]
/-
**is_ideal_adic_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : Nat} (hn : 0 < n) : Is
Adic (J ^ n)
参数：h : IsAdic J；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAdic_iff`：isAdic_iff [top : TopologicalSpace R] [IsTopologicalRing R] 
{J : Ideal R} : IsAdic J ↔ (forall n : Nat, IsOpen ((J ^ n : Ideal R) : Set R)) 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Nat.not_succ_le_zero`：∀ (n : ℕ), n.succ ≤ 0 → False
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : ℕ} (hn : 0 < n) : IsAdic (J ^ n) := by
  rw [isAdic_iff] at h ⊢
  constructor
  · intro m
    rw [← pow_mul]
    apply h.left
  · intro V hV
    obtain ⟨m, hm⟩ := h.right V hV
    use m
    refine Set.Subset.trans ?_ hm
    cases n
    · exfalso
      exact Nat.not_succ_le_zero 0 hn
    rw [← pow_mul, Nat.succ_mul]
    apply Ideal.pow_le_pow_right
    apply Nat.le_add_left
/-
**is_bot_adic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is_bot_adic_iff {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologic
alRing A] : IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAdic_iff`：isAdic_iff [top : TopologicalSpace R] [IsTopologicalRing R] 
{J : Ideal R} : IsAdic J ↔ (forall n : Nat, IsOpen ((J ^ n : Ideal R) : Set R)) 
…
· 使用定理 `discreteTopology_iff_isOpen_singleton_zero`：∀ {G : Type w} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G],   DiscreteTopo
logy G ↔ IsOpen {0}
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem is_bot_adic_iff {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A := by
  rw [isAdic_iff]
  constructor
  · rintro ⟨h, _h'⟩
    rw [discreteTopology_iff_isOpen_singleton_zero]
    simpa using h 1
  · intros
    constructor
    · simp
    · intro U U_nhds
      use 1
      simp [mem_of_mem_nhds U_nhds]

omit [IsTopologicalRing R] in
/-
**IsAdic.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAdic.hasBasis_nhds_zero {I : Ideal R} (hI : IsAdic I) : (𝓝 (0 : R)).HasB
asis (fun _ => True) fun n => ↑(I ^ n)
参数：hI : IsAdic I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.hasBasis_nhds_zero_adic`：hasBasis_nhds_zero_adic (I : Ideal R) : H
asBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n => ((I ^ n
 : Ideal R) : Set R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsAdic.hasBasis_nhds_zero {I : Ideal R} (hI : IsAdic I) :
    (𝓝 (0 : R)).HasBasis (fun _ ↦ True) fun n ↦ ↑(I ^ n) :=
  hI ▸ Ideal.hasBasis_nhds_zero_adic I

omit [IsTopologicalRing R] in
/-
**IsAdic.hasBasis_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAdic.hasBasis_nhds {I : Ideal R} (hI : IsAdic I) (x : R) : (𝓝 x).HasBasi
s (fun _ => True) fun n => (x + ·) '' ↑(I ^ n)
参数：hI : IsAdic I；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.hasBasis_nhds_adic`：hasBasis_nhds_adic (I : Ideal R) (x : R) : Has
Basis (@nhds R I.adicTopology x) (fun _n : Nat => True) fun n => (fun y => x + y
) '' (I ^ n : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsAdic.hasBasis_nhds {I : Ideal R} (hI : IsAdic I) (x : R) :
    (𝓝 x).HasBasis (fun _ ↦ True) fun n ↦ (x + ·) '' ↑(I ^ n) :=
  hI ▸ Ideal.hasBasis_nhds_adic I x

end IsAdic

/-- The ring `R` is equipped with a preferred ideal. -/
/-
**WithIdeal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [CommRing R] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `R` is equipped with a preferred ideal.
-/
class WithIdeal (R : Type*) [CommRing R] where
  i : Ideal R

namespace WithIdeal

variable (R)
variable [WithIdeal R]

/-
**WithIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : TopologicalSpace R :=
  i.adicTopology
/-
**WithIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : NonarchimedeanRing R :=
  RingSubgroupsBasis.nonarchimedean _
/-
**WithIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : UniformSpace R :=
  IsTopologicalAddGroup.rightUniformSpace R
/-
**WithIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsUniformAddGroup R :=
  isUniformAddGroup_of_addCommGroup
/-
**WithIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsLinearTopology R R := i.isLinearTopology

variable {R} in
/-
**WithIdeal.uniformContinuous_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 `WithIdeal`。
形式化陈述：uniformContinuous_of_map_le {S : Type*} [CommRing S] [WithIdeal S] {f : R 
->+* S} (hf : i.map f <= i) : UniformContinuous f
参数：hf : i.map f <= i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `WithIdeal.instIsUniformAddGroup`：∀ (R : Type u_1) [inst : CommRing R] [i
nst_1 : WithIdeal R], IsUniformAddGroup R
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Ideal.hasBasis_nhds_zero_adic`：hasBasis_nhds_zero_adic (I : Ideal R) : H
asBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n => ((I ^ n
 : Ideal R) : Set R…
· 使用定理 `trivial`：True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `Ideal.pow_right_mono`：pow_right_mono (e : I <= J) (n : Nat) : I ^ n <= J
 ^ n
-/
theorem uniformContinuous_of_map_le {S : Type*} [CommRing S] [WithIdeal S] {f : R →+* S}
    (hf : i.map f ≤ i) : UniformContinuous f := uniformContinuous_of_continuousAt_zero f (by
  rw [ContinuousAt, map_zero, i.hasBasis_nhds_zero_adic.tendsto_iff i.hasBasis_nhds_zero_adic]
  refine fun n _ ↦ ⟨n, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
  simpa [Ideal.map_pow] using Ideal.pow_right_mono hf n)

variable {R} in
/-- A ring equivalence induces a uniform equivalence with respect to the adic topologies,
provided it preserves the defining ideals. -/
/-
**WithIdeal.uniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithIdeal`。
形式化陈述：uniformEquiv {S : Type*} [CommRing S] [WithIdeal S] (e : R ≃+* S) (h : i.m
ap e.toRingHom = i) : UniformEquiv R S where __
参数：e : R ≃+* S；h : i.map e.toRingHom = i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring equivalence induces a uniform equivalence with respect to the adic topolo
gies,
provided it preserves the defining ideals.
-/
def uniformEquiv {S : Type*} [CommRing S] [WithIdeal S] (e : R ≃+* S)
    (h : i.map e.toRingHom = i) : UniformEquiv R S where
  __ := e
  uniformContinuous_toFun := uniformContinuous_of_map_le (f := e.toRingHom) (by rw [h])
  uniformContinuous_invFun := uniformContinuous_of_map_le (f := e.symm.toRingHom) (by simp [← h])

variable {R} in
/-
**WithIdeal.isTopologicallyNilpotent_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `WithIdeal
`。
形式化陈述：isTopologicallyNilpotent_of_mem {a : R} (ha : a in i) : IsTopologicallyNil
potent a
参数：ha : a in i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Ideal.hasBasis_nhds_zero_adic`：hasBasis_nhds_zero_adic (I : Ideal R) : H
asBasis (@nhds R I.adicTopology (0 : R)) (fun _n : Nat => True) fun n => ((I ^ n
 : Ideal R) : Set R…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma isTopologicallyNilpotent_of_mem {a : R} (ha : a ∈ i) : IsTopologicallyNilpotent a := by
  suffices ∀ m : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → a ^ n ∈ i ^ m by
    simpa [IsTopologicallyNilpotent, i.hasBasis_nhds_zero_adic.tendsto_right_iff]
  exact fun m ↦ ⟨m, fun n hn ↦ Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

/-- The adic topology on an `R` module coming from the ideal `WithIdeal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
@[instance_reducible]
/-
**WithIdeal.topologicalSpaceModule** 是 Mathlib 中的一个定义，位于命名空间 `WithIdeal`。
形式化陈述：topologicalSpaceModule (M : Type*) [AddCommGroup M] [Module R M] : Topolog
icalSpace M
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adic topology on an `R` module coming from the ideal `WithIdeal.I`.
This cannot be an instance because `R` cannot be inferred from `M`.
-/
def topologicalSpaceModule (M : Type*) [AddCommGroup M] [Module R M] : TopologicalSpace M :=
  (i : Ideal R).adicModuleTopology M

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/
/-
**WithIdeal.** 是 Mathlib 中的一个示例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The next examples are kept to make sure potential future refactors won't break t
he instance
chaining.
-/
example : NonarchimedeanRing R := by infer_instance
/-
**WithIdeal.** 是 Mathlib 中的一个示例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsTopologicalRing (UniformSpace.Completion R) := by infer_instance
/-
**WithIdeal.** 是 Mathlib 中的一个示例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (M : Type*) [AddCommGroup M] [Module R M] :
    @IsTopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ := by infer_instance
/-
**WithIdeal.** 是 Mathlib 中的一个示例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (M : Type*) [AddCommGroup M] [Module R M] :
    @ContinuousSMul R M _ _ (WithIdeal.topologicalSpaceModule R M) := by infer_instance
/-
**WithIdeal.** 是 Mathlib 中的一个示例，位于命名空间 `WithIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (M : Type*) [AddCommGroup M] [Module R M] :
    @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _

end WithIdeal

