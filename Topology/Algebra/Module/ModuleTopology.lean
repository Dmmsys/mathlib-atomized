/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Will Sawin
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Group.Basic

/-!
# A "module topology" for modules over a topological ring

If `R` is a topological ring acting on an additive abelian group `A`, we define the
*module topology* to be the finest topology on `A` making both the maps
`• : R × A → A` and `+ : A × A → A` continuous (with all the products having the
product topology). Note that `- : A → A` is also automatically continuous as it is `a ↦ (-1) • a`.

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).


## Mathematical details

I (buzzard) don't know of any reference for this other than Sawin's mathoverflow answer,
so I expand some of the details here.

First note that the definition makes sense in far more generality (for example `R` just needs to
be a topological space acting on an additive monoid).

Next note that there *is* a finest topology with this property! Indeed, topologies on a fixed
type form a complete lattice (infinite infs and sups exist). So if `τ` is the Inf of all
the topologies on `A` which make `+` and `•` continuous, then the claim is that `+` and `•`
are still continuous for `τ` (note that topologies are ordered so that finer topologies
are smaller). To show `+ : A × A → A` is continuous we equivalently need to show
that the pushforward of the product topology `τ × τ` along `+` is `≤ τ`, and because `τ` is
the greatest lower bound of the topologies making `•` and `+` continuous,
it suffices to show that it's `≤ σ` for any topology `σ` on `A` which makes `+` and `•` continuous.
However pushforward and products are monotone, so `τ × τ ≤ σ × σ`, and the pushforward of
`σ × σ` is `≤ σ` because that's precisely the statement that `+` is continuous for `σ`.
The proof for `•` follows mutatis mutandis.

A *topological module* for a topological ring `R` is an `R`-module `A` with a topology
making `+` and `•` continuous. The discussion so far has shown that the module topology makes
an `R`-module `A` into a topological module, and moreover is the finest topology with this property.

A crucial observation is that if `M` is a topological `R`-module, if `A` is an `R`-module with no
topology, and if `φ : A → M` is linear, then the pullback of `M`'s topology to `A` is a topology
making `A` into a topological module. Let's for example check that `•` is continuous.
If `U ⊆ A` is open then by definition of the pullback topology, `U = φ⁻¹(V)` for some open `V ⊆ M`,
and now the pullback of `U` under `•` is just the pullback along the continuous map
`id × φ : R × A → R × M` of the preimage of `V` under the continuous map `• : R × M → M`,
so it's open. The proof for `+` is similar.

As a consequence of this, we see that if `φ : A → M` is a linear map between topological `R`-modules
modules and if `A` has the module topology, then `φ` is automatically continuous.
Indeed the argument above shows that if `A → M` is linear then the module
topology on `A` is `≤` the pullback of the module topology on `M` (because it's the inf of a set
containing this topology) which is the definition of continuity.

We also deduce that the module topology is a functor from the category of `R`-modules
(`R` a topological ring) to the category of topological `R`-modules, and it is perhaps
unsurprising that this is an adjoint to the forgetful functor. Indeed, if `A` is an `R`-module
and `M` is a topological `R`-module, then the previous paragraph shows that
the linear maps `A → M` are precisely the continuous linear maps
from (`A` with its module topology) to `M`, so the module topology is a left adjoint
to the forgetful functor.

This file develops the theory of the module topology.

## Main theorems

* `IsTopologicalSemiring.toIsModuleTopology : IsModuleTopology R R`. The module
    topology on `R` is `R`'s topology.
* `IsModuleTopology.iso [IsModuleTopology R A] (e : A ≃L[R] B) : IsModuleTopology R B`. If `A` and
    `B` are `R`-modules with topologies, if `e` is a topological isomorphism between them,
    and if `A` has the module topology, then `B` has the module topology.
* `IsModuleTopology.instProd` : If `M` and `N` are `R`-modules each equipped with the module
  topology, then the product topology on `M × N` is the module topology.
* `IsModuleTopology.instPi` : Given a finite collection of `R`-modules each of which has
  the module topology, the product topology on the product module is the module topology.
* `IsModuleTopology.isTopologicalRing` : If `D` is an `R`-algebra equipped with the module
  topology, and `D` is finite as an `R`-module, then `D` is a topological ring (that is,
  addition, negation and multiplication are continuous).

Now say `φ : A →ₗ[R] B` is an `R`-linear map between `R`-modules equipped with
the module topology.

* `IsModuleTopology.continuous_of_linearMap φ` is the proof that `φ` is automatically
  continuous.
* `IsModuleTopology.isQuotientMap_of_surjective (hφ : Function.Surjective φ)`
  is the proof that if furthermore `φ` is surjective then it is a quotient map,
  that is, the module topology on `B` is the pushforward of the module topology
  on `A`.

Now say `ψ : A →ₗ[R] B →ₗ[R] C` is an `R`-bilinear map between `R`-modules equipped with
the module topology.

* `IsModuleTopology.continuous_bilinear_of_finite_left` : If `A` is finite then `A × B → C`
  is continuous.
* `IsModuleTopology.continuous_bilinear_of_finite_right` : If `B` is finite then `A × B → C`
  is continuous.

## TODO

* The module topology is a functor from the category of `R`-modules
  to the category of topological `R`-modules, and it's an adjoint to the forgetful functor.

-/

public section

section basics

/-
This section is just boilerplate, defining the module topology and making
some infrastructure. Note that we don't even need that `R` is a ring
in the main definitions, just that it acts on `A`.
-/
variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

/-- The module topology, for a module `A` over a topological ring `R`. It's the finest topology
making addition and the `R`-action continuous, or equivalently the finest topology making `A`
into a topological `R`-module. More precisely it's the Inf of the set of
topologies with these properties; theorems `continuousSMul` and `continuousAdd` show
that the module topology also has these properties. -/
/-
**moduleTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：moduleTopology : TopologicalSpace A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The module topology, for a module `A` over a topological ring `R`. It's the fine
st topology
making addition and the `R`-action continuous, or equivalently the finest topolo
gy making `A`
into a topological `R`-module. More precisely it's the Inf of the set of
topologies with these properties; theorems `continuousSMul` and `continuousAdd` 
show
that the module topology also has these properties.
-/
abbrev moduleTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

/-- A class asserting that the topology on a module over a topological ring `R` is
the module topology. See `moduleTopology` for more discussion of the module topology. -/
/-
**IsModuleTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [TopologicalSpace R] → (A : Type u_2) → [Add A] → [SMul R
 A] → [τA : TopologicalSpace A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class asserting that the topology on a module over a topological ring `R` is
the module topology. See `moduleTopology` for more discussion of the module topo
logy.
-/
class IsModuleTopology [τA : TopologicalSpace A] : Prop where
  /-- Note that this should not be used directly, and `eq_moduleTopology`, which takes `R` and `A`
  explicitly, should be used instead. -/
  eq_moduleTopology' : τA = moduleTopology R A
/-
**eq_moduleTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_moduleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] : τA = 
moduleTopology R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.eq_moduleTopology'`：∀ {R : Type u_1} {inst : Topologica
lSpace R} {A : Type u_2} {inst_1 : Add A} {inst_2 : SMul R A}   {τA : Topologica
lSpace A} [self : IsModul…
-/
theorem eq_moduleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] :
    τA = moduleTopology R A :=
  IsModuleTopology.eq_moduleTopology' (R := R) (A := A)

/--
Note that the topology isn't part of the discrimination key so this gets tried on every
`IsModuleTopology` goal and hence the low priority.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the topology isn't part of the discrimination key so this gets tried o
n every
`IsModuleTopology` goal and hence the low priority.
-/
instance (priority := low) {R : Type*} [TopologicalSpace R] {A : Type*} [Add A] [SMul R A] :
    letI := moduleTopology R A; IsModuleTopology R A :=
  letI := moduleTopology R A; ⟨rfl⟩

/-- Scalar multiplication `• : R × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the module topology. -/
/-
**ModuleTopology.continuousSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModuleTopology.continuousSMul : @ContinuousSMul R A _ _ (moduleTopology R 
A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousSMul_sInf`：continuousSMul_sInf {ts : Set (TopologicalSpace X)}
 (h : forall t in ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (sInf
 ts)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Scalar multiplication `• : R × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the module topology.
-/
theorem ModuleTopology.continuousSMul : @ContinuousSMul R A _ _ (moduleTopology R A) :=
  /- Proof: We need to prove that the product topology is finer than the pullback
     of the module topology. But the module topology is an Inf and thus a limit,
     and pullback is a right adjoint, so it preserves limits.
     We must thus show that the product topology is finer than an Inf, so it suffices
     to show it's a lower bound, which is not hard. All this is wrapped into
     `continuousSMul_sInf`.
  -/
  continuousSMul_sInf fun _ h ↦ h.1

/-- Addition `+ : A × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the module topology. -/
/-
**ModuleTopology.continuousAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModuleTopology.continuousAdd : @ContinuousAdd A (moduleTopology R A) _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAdd_sInf`：∀ {M : Type u_3} [inst : Add M] {ts : Set (Topologic
alSpace M)}, (∀ t ∈ ts, ContinuousAdd M) → ContinuousAdd M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Addition `+ : A × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the module topology.
-/
theorem ModuleTopology.continuousAdd : @ContinuousAdd A (moduleTopology R A) _ :=
  continuousAdd_sInf fun _ h ↦ h.2
/-
**IsModuleTopology.toContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsModuleTopology.toContinuousSMul [TopologicalSpace A] [IsModuleTopology R
 A] : ContinuousSMul R A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleTopology.continuousSMul`：ModuleTopology.continuousSMul : @Continuo
usSMul R A _ _ (moduleTopology R A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_moduleTopology`：eq_moduleTopology [τA : TopologicalSpace A] [IsModule
Topology R A] : τA = moduleTopology R A
-/
instance IsModuleTopology.toContinuousSMul [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousSMul R A := eq_moduleTopology R A ▸ ModuleTopology.continuousSMul R A

-- this can't be an instance because typeclass inference can't be expected to find `R`.
/-
**IsModuleTopology.toContinuousAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsModuleTopology.toContinuousAdd [TopologicalSpace A] [IsModuleTopology R 
A] : ContinuousAdd A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleTopology.continuousAdd`：ModuleTopology.continuousAdd : @Continuous
Add A (moduleTopology R A) _
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_moduleTopology`：eq_moduleTopology [τA : TopologicalSpace A] [IsModule
Topology R A] : τA = moduleTopology R A
-/
theorem IsModuleTopology.toContinuousAdd [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousAdd A := eq_moduleTopology R A ▸ ModuleTopology.continuousAdd R A

/-- The module topology is `≤` any topology making `A` into a topological module. -/
/-
**moduleTopology_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：moduleTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [Continuo
usAdd A] : moduleTopology R A <= τA
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
The module topology is `≤` any topology making `A` into a topological module.
-/
theorem moduleTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    moduleTopology R A ≤ τA := sInf_le ⟨inferInstance, inferInstance⟩

end basics

namespace IsModuleTopology

section basics

variable {R : Type*} [TopologicalSpace R]
  {A : Type*} [Add A] [SMul R A] [τA : TopologicalSpace A]

/-- If `A` is a topological `R`-module and the identity map from (`A` with its given
topology) to (`A` with the module topology) is continuous, then the topology on `A` is
the module topology. -/
/-
**IsModuleTopology.of_continuous_id** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopology`
。
形式化陈述：of_continuous_id [ContinuousAdd A] [ContinuousSMul R A] (h : @Continuous A
 A τA (moduleTopology R A) id) : IsModuleTopology R A where -- The topologies ar
e equal because each is finer than the other. One inclusion -- follows from the 
continuity hypothesis; the other is because the module topology -- is the inf of
 all the topologies making `A` a topological module. eq_moduleTopology'
参数：h : @Continuous A A τA (moduleTopology R A) id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_id_iff_le`：continuous_id_iff_le {t t' : TopologicalSpace α} :
 Continuous[t, t'] id ↔ t <= t'
· 使用定理 `moduleTopology_le`：moduleTopology_le [τA : TopologicalSpace A] [Continuo
usSMul R A] [ContinuousAdd A] : moduleTopology R A <= τA

--- 原说明 ---
If `A` is a topological `R`-module and the identity map from (`A` with its given
topology) to (`A` with the module topology) is continuous, then the topology on 
`A` is
the module topology.
-/
theorem of_continuous_id [ContinuousAdd A] [ContinuousSMul R A]
    (h : @Continuous A A τA (moduleTopology R A) id) :
    IsModuleTopology R A where
  -- The topologies are equal because each is finer than the other. One inclusion
  -- follows from the continuity hypothesis; the other is because the module topology
  -- is the inf of all the topologies making `A` a topological module.
  eq_moduleTopology' := le_antisymm (continuous_id_iff_le.1 h) (moduleTopology_le _ _)

/-- The zero module has the module topology. -/
/-
**IsModuleTopology.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `IsModuleTopology`
。
形式化陈述：instSubsingleton [Subsingleton A] : IsModuleTopology R A where eq_moduleTo
pology'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The zero module has the module topology.
-/
instance instSubsingleton [Subsingleton A] : IsModuleTopology R A where
  eq_moduleTopology' := Subsingleton.elim _ _

end basics

section iso

variable {R S : Type*} [τR : TopologicalSpace R] [τS : TopologicalSpace S] [Semiring R] [Semiring S]
variable {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]
variable {B' : Type*} [AddCommMonoid B'] [Module S B'] [τB' : TopologicalSpace B']

/-- If `A` and `B` are modules, homeomorphic via a semilinear homeomorphism, and if
`A` has the module topology, then so does `B`. -/
/-
**IsModuleTopology.iso** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopology`。
形式化陈述：∀ {R : Type u_1} [τR : TopologicalSpace R] [inst : Semiring R] {A : Type u
_3} [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [τA : TopologicalS
pace A] [IsModuleTopology R A] {B : Type u_4}   [inst_4 : AddCommMonoid B] [inst
_5 : _root_.Module R B] [τB : TopologicalSpace B] (e : A ≃L[R] B),   IsModuleTop
ology R B
参数：e : A ≃L[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isoₛₗ`：∀ {R : Type u_1} {S : Type u_2} [τR : Topologica
lSpace R] [τS : TopologicalSpace S] [inst : Semiring R]   [inst_1 : Semiring S] 
{σ : R →+* S…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If `A` and `B` are modules, homeomorphic via a semilinear homeomorphism, and if
`A` has the module topology, then so does `B`.
-/
protected theorem isoₛₗ (hσ : Continuous σ) (hσ' : Continuous σ') (e : A ≃SL[σ] B') :
    IsModuleTopology S B' where
  eq_moduleTopology' := by
    -- get these in before I start putting new topologies on A and B and have to use `@`
    let g : A →ₛₗ[σ] B' := e
    let g' : B' →ₛₗ[σ'] A := e.symm
    let h : A →+ B' := e
    let h' : B' →+ A := e.symm
    simp_rw [e.toHomeomorph.symm.isInducing.1, eq_moduleTopology R A, moduleTopology, induced_sInf]
    apply congr_arg
    ext τ -- from this point on the definitions of `g`, `g'` etc. above don't work without `@`.
    rw [Set.mem_image]
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      exact ⟨continuousSMul_inducedₛₗ g' hσ', continuousAdd_induced h'⟩
    · rintro ⟨h1, h2⟩
      use τ.induced e
      rw [induced_compose]
      refine ⟨⟨continuousSMul_inducedₛₗ g hσ, continuousAdd_induced h⟩, ?_⟩
      nth_rw 2 [← induced_id (t := τ)]
      simp

/-- If `A` and `B` are `R`-modules, homeomorphic via an `R`-linear homeomorphism, and if
`A` has the module topology, then so does `B`.
See `IsModuleTopology.isoₛₗ` for the generalization to a semilinear homeomorphism. -/
/-
**IsModuleTopology.iso** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopology`。
形式化陈述：∀ {R : Type u_1} [τR : TopologicalSpace R] [inst : Semiring R] {A : Type u
_3} [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [τA : TopologicalS
pace A] [IsModuleTopology R A] {B : Type u_4}   [inst_4 : AddCommMonoid B] [inst
_5 : _root_.Module R B] [τB : TopologicalSpace B] (e : A ≃L[R] B),   IsModuleTop
ology R B
参数：e : A ≃L[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isoₛₗ`：∀ {R : Type u_1} {S : Type u_2} [τR : Topologica
lSpace R] [τS : TopologicalSpace S] [inst : Semiring R]   [inst_1 : Semiring S] 
{σ : R →+* S…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If `A` and `B` are `R`-modules, homeomorphic via an `R`-linear homeomorphism, an
d if
`A` has the module topology, then so does `B`.
See `IsModuleTopology.isoₛₗ` for the generalization to a semilinear homeomorphis
m.
-/
protected theorem iso (e : A ≃L[R] B) : IsModuleTopology R B :=
  IsModuleTopology.isoₛₗ continuous_id continuous_id e

end iso

section self

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [IsTopologicalSemiring R]

/-!
We now fix once and for all a topological semiring `R`.

We first prove that the module topology on `R` considered as a module over itself,
is `R`'s topology.
-/

-- see Note [higher instance priority]
/-- The topology on a topological semiring `R` agrees with the module topology when considering
`R` as an `R`-module in the obvious way (i.e., via `Semiring.toModule`). -/
/-
**IsModuleTopology.** 是 Mathlib 中的一个实例，位于命名空间 `IsModuleTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on a topological semiring `R` agrees with the module topology when 
considering
`R` as an `R`-module in the obvious way (i.e., via `Semiring.toModule`).
-/
instance (priority := 1100) _root_.IsTopologicalSemiring.toIsModuleTopology :
    IsModuleTopology R R := by
  /- By a previous lemma it suffices to show that the identity from (R,usual) to
  (R, module topology) is continuous. -/
  apply of_continuous_id
  /-
  The idea needed here is to rewrite the identity function as the composite of `r ↦ (r,1)`
  from `R` to `R × R`, and multiplication `R × R → R`.
  -/
  rw [show (id : R → R) = (fun rs ↦ rs.1 • rs.2) ∘ (fun r ↦ (r, 1)) by ext; simp]
  /-
  It thus suffices to show that each of these maps are continuous. For this claim to even make
  sense, we need to topologise `R × R`. The trick is to do this by giving the first `R` the usual
  topology `τR` and the second `R` the module topology. To do this we have to "fight mathlib"
  a bit with `@`, because there is more than one topology on `R` here.
  -/
  apply @Continuous.comp R (R × R) R τR (@instTopologicalSpaceProd R R τR (moduleTopology R R))
      (moduleTopology R R)
  · /-
    The map R × R → R is `•`, so by a fundamental property of the module topology,
    this is continuous. -/
    exact @continuous_smul _ _ _ _ (moduleTopology R R) <| ModuleTopology.continuousSMul ..
  · /-
    The map `R → R × R` sending `r` to `(r,1)` is a map into a product, so it suffices to show
    that each of the two factors is continuous. But the first is the identity function
    on `(R, usual topology)` and the second is a constant function. -/
    exact @Continuous.prodMk _ _ _ _ (moduleTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (moduleTopology R R) _

end self

section MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [IsTopologicalSemiring R]

/-- The module topology coming from the action of the topological ring `Rᵐᵒᵖ` on `R`
  (via `Semiring.toOppositeModule`, i.e. via `(op r) • m = m * r`) is `R`'s topology. -/
/-
**IsModuleTopology._root_.IsTopologicalSemiring.toOppositeIsModuleTopology** 是 M
athlib 中的一个实例，位于命名空间 `IsModuleTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The module topology coming from the action of the topological ring `Rᵐᵒᵖ` on `R`
  (via `Semiring.toOppositeModule`, i.e. via `(op r) • m = m * r`) is `R`'s topo
logy.
-/
instance _root_.IsTopologicalSemiring.toOppositeIsModuleTopology : IsModuleTopology Rᵐᵒᵖ R :=
  .iso (MulOpposite.opContinuousLinearEquiv Rᵐᵒᵖ).symm

end MulOpposite

section function

variable {R S : Type*} [τR : TopologicalSpace R] [τS : TopologicalSpace S] [Semiring R] [Semiring S]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B]
    [ContinuousAdd B] [ContinuousSMul R B]
variable {B' : Type*} [AddCommMonoid B'] [Module S B'] [aB' : TopologicalSpace B']
    [ContinuousAdd B'] [ContinuousSMul S B']

/-- Every semilinear map between two topological modules, where the source has the module
topology, is continuous. -/
-- `fun_prop` can't use this; e.g. `continuous_of_distribMulActionHom` is not proved by `fun_prop`
@[continuity]
/-
**IsModuleTopology.continuous_of_distribMulActionHom** 是 Mathlib 中的一个定理，位于命名空间 `
IsModuleTopology`。
形式化陈述：continuous_of_distribMulActionHom (φ : A ->+[R] B) : Continuous φ
参数：φ : A ->+[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_of_distribMulActionHomₑ`：continuous_of_distr
ibMulActionHomₑ {σ : R ->* S} (hσ : Continuous σ) (φ : A ->ₑ+[σ] B') : Continuou
s φ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_of_distribMulActionHomₑ {σ : R →* S} (hσ : Continuous σ) (φ : A →ₑ+[σ] B') :
    Continuous φ := by
  -- the proof: We know that `+ : B × B → B` and `• : R × B → B` are continuous for the module
  -- topology on `B`, and two earlier theorems (`continuousSMul_induced` and
  -- `continuousAdd_induced`) say that hence `+` and `•` on `A` are continuous if `A`
  -- is given the topology induced from `φ`. Hence the module topology is finer than
  -- the induced topology, and so the function is continuous.
  rw [eq_moduleTopology R A, continuous_iff_le_induced]
  exact sInf_le <| ⟨continuousSMul_inducedₛₗ φ hσ, continuousAdd_induced φ⟩

/-- Every `R`-linear map between two topological `R`-modules, where the source has the module
topology, is continuous. -/
@[fun_prop]
/-
**IsModuleTopology.continuous_of_distribMulActionHom** 是 Mathlib 中的一个定理，位于命名空间 `
IsModuleTopology`。
形式化陈述：continuous_of_distribMulActionHom (φ : A ->+[R] B) : Continuous φ
参数：φ : A ->+[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_of_distribMulActionHomₑ`：continuous_of_distr
ibMulActionHomₑ {σ : R ->* S} (hσ : Continuous σ) (φ : A ->ₑ+[σ] B') : Continuou
s φ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
Every `R`-linear map between two topological `R`-modules, where the source has t
he module
topology, is continuous.
-/
theorem continuous_of_distribMulActionHom (φ : A →+[R] B) : Continuous φ :=
  continuous_of_distribMulActionHomₑ continuous_id φ

/-- Every semilinear map between two topological modules, where the source has the module
topology, is continuous. -/
-- `fun_prop` can't use this; e.g. `continuous_of_linearMap` is not proved by `fun_prop`
@[continuity]
/-
**IsModuleTopology.continuous_of_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTo
pology`。
形式化陈述：continuous_of_linearMap (φ : A ->ₗ[R] B) : Continuous φ
参数：φ : A ->ₗ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_of_distribMulActionHom`：continuous_of_distri
bMulActionHom (φ : A ->+[R] B) : Continuous φ
-/
theorem continuous_of_linearMapₛₗ {σ : R →+* S} (hσ : Continuous σ) (φ : A →ₛₗ[σ] B') :
    Continuous φ :=
  continuous_of_distribMulActionHomₑ hσ φ.toDistribMulActionHom

/-- Every `R`-linear map between two topological `R`-modules, where the source has the module
topology, is continuous. -/
@[fun_prop]
/-
**IsModuleTopology.continuous_of_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTo
pology`。
形式化陈述：continuous_of_linearMap (φ : A ->ₗ[R] B) : Continuous φ
参数：φ : A ->ₗ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_of_distribMulActionHom`：continuous_of_distri
bMulActionHom (φ : A ->+[R] B) : Continuous φ

--- 原说明 ---
Every `R`-linear map between two topological `R`-modules, where the source has t
he module
topology, is continuous.
-/
theorem continuous_of_linearMap (φ : A →ₗ[R] B) : Continuous φ :=
  continuous_of_distribMulActionHom φ.toDistribMulActionHom

variable (R) in
/-
**IsModuleTopology.continuous_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopology`。
形式化陈述：continuous_neg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace
 C] [IsModuleTopology R C] : Continuous (fun a => -a : C -> C)
参数：C : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `IsModuleTopology.toContinuousAdd`：IsModuleTopology.toContinuousAdd [Topo
logicalSpace A] [IsModuleTopology R A] : ContinuousAdd A
-/
theorem continuous_neg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : Continuous (fun a ↦ -a : C → C) :=
  haveI : ContinuousAdd C := IsModuleTopology.toContinuousAdd R C
  continuous_of_linearMap (LinearEquiv.neg R).toLinearMap

variable (R) in
/-
**IsModuleTopology.continuousNeg** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopology`。
形式化陈述：continuousNeg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace 
C] [IsModuleTopology R C] : ContinuousNeg C where continuous_neg
参数：C : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_neg`：continuous_neg (C : Type*) [AddCommGrou
p C] [Module R C] [TopologicalSpace C] [IsModuleTopology R C] : Continuous (fun 
a => -a : C -> C)
-/
theorem continuousNeg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : ContinuousNeg C where
  continuous_neg := continuous_neg R C

variable (R) in
/-
**IsModuleTopology.topologicalAddGroup** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopolo
gy`。
形式化陈述：topologicalAddGroup (C : Type*) [AddCommGroup C] [Module R C] [Topological
Space C] [IsModuleTopology R C] : IsTopologicalAddGroup C where continuous_add
参数：C : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.toContinuousAdd`：IsModuleTopology.toContinuousAdd [Topo
logicalSpace A] [IsModuleTopology R A] : ContinuousAdd A
· 使用定理 `IsModuleTopology.continuous_neg`：continuous_neg (C : Type*) [AddCommGrou
p C] [Module R C] [TopologicalSpace C] [IsModuleTopology R C] : Continuous (fun 
a => -a : C -> C)
-/
theorem topologicalAddGroup (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : IsTopologicalAddGroup C where
  continuous_add := (IsModuleTopology.toContinuousAdd R C).1
  continuous_neg := continuous_neg R C

@[fun_prop, continuity]
/-
**IsModuleTopology.continuous_of_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopo
logy`。
形式化陈述：continuous_of_ringHom {R A B} [CommSemiring R] [Semiring A] [Algebra R A] 
[Semiring B] [TopologicalSpace R] [TopologicalSpace A] [IsModuleTopology R A] [T
opologicalSpace B] [IsTopologicalSemiring B] (φ : A ->+* B) (hφ : Continuous (φ.
comp (algebraMap R A))) : Continuous φ
参数：φ : A ->+* B；hφ : Continuous (φ.comp (algebraMap R A))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
-/
theorem continuous_of_ringHom {R A B} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [TopologicalSpace R] [TopologicalSpace A] [IsModuleTopology R A] [TopologicalSpace B]
    [IsTopologicalSemiring B]
    (φ : A →+* B) (hφ : Continuous (φ.comp (algebraMap R A))) : Continuous φ := by
  let inst := Module.compHom B (φ.comp (algebraMap R A))
  let φ' : A →ₗ[R] B := ⟨φ, fun r m ↦ by simp [Algebra.smul_def]; rfl⟩
  have : ContinuousSMul R B := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  exact continuous_of_linearMap φ'

end function

section surjection

variable {R S : Type*} [τR : TopologicalSpace R] [τS : TopologicalSpace S] [Ring R] [Ring S]
variable {A : Type*} [AddCommGroup A] [Module R A] [TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B]
variable {B' : Type*} [AddCommGroup B'] [Module S B']

open Topology in
/-- A semilinear surjection between modules with the module topology is a quotient map.
Equivalently, the pushforward of the module topology along a surjective semilinear map is
again the module topology. -/
/-
**IsModuleTopology.isQuotientMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsModu
leTopology`。
形式化陈述：isQuotientMap_of_surjective [τB : TopologicalSpace B] [IsModuleTopology R 
B] {φ : A ->ₗ[R] B} (hφ : Function.Surjective φ) : IsQuotientMap φ
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isQuotientMap_of_surjectiveₛₗ`：isQuotientMap_of_surject
iveₛₗ [τB : TopologicalSpace B'] [IsModuleTopology S B'] {σ : R ->+* S} (hσ : Is
OpenQuotientMap σ) (φ : A ->ₛₗ[σ] B'…
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id

--- 原说明 ---
A semilinear surjection between modules with the module topology is a quotient m
ap.
Equivalently, the pushforward of the module topology along a surjective semiline
ar map is
again the module topology.
-/
theorem isQuotientMap_of_surjectiveₛₗ [τB : TopologicalSpace B'] [IsModuleTopology S B']
    {σ : R →+* S} (hσ : IsOpenQuotientMap σ) (φ : A →ₛₗ[σ] B') (hφ : Function.Surjective φ) :
    IsQuotientMap φ where
  surjective := hφ
  eq_coinduced := by
    -- We need to prove that the topology on B is coinduced from that on A.
    -- First tell the typeclass inference system that A and B are topological groups.
    have := IsModuleTopology.toContinuousAdd R A
    have := IsModuleTopology.toContinuousAdd S B'
    -- Because φ is linear, it's continuous for the module topologies (by a previous result).
    have : Continuous φ := continuous_of_linearMapₛₗ hσ.continuous φ
    -- So the coinduced topology is finer than the module topology on B.
    rw [continuous_iff_coinduced_le] at this
    -- So STP the module topology on B is ≤ the topology coinduced from A
    refine le_antisymm ?_ this
    rw [eq_moduleTopology S B']
    -- Now let's remove B's topology from the typeclass system
    clear! τB
    -- and replace it with the coinduced topology (which will be the same, but that's what we're
    -- trying to prove). This means we don't have to fight with the typeclass system.
    let : TopologicalSpace B' := .coinduced φ inferInstance
    -- With this new topology on `B`, φ is a quotient map by definition,
    -- and hence an open quotient map by a result in the library.
    have hφo : IsOpenQuotientMap φ := AddMonoidHom.isOpenQuotientMap_of_isQuotientMap ⟨⟨rfl⟩, hφ⟩
    -- We're trying to prove the module topology on B is ≤ the coinduced topology.
    -- But recall that the module topology is the Inf of the topologies on B making addition
    -- and scalar multiplication continuous, so it suffices to prove
    -- that the coinduced topology on B has these properties.
    refine sInf_le ⟨?_, ?_⟩
    · -- In this branch, we prove that `• : S × B → B` is continuous for the coinduced topology.
      apply ContinuousSMul.mk
      -- We know that `• : R × A → A` is continuous, by assumption.
      obtain ⟨hA⟩ : ContinuousSMul R A := inferInstance
      /- By linearity of φ, this diagram commutes:
        R × A --(•)--> A
          |            |
          |σ × φ      |φ
          |            |
         \/            \/
        S × B --(•)--> B
      -/
      have hφ2 : (fun p ↦ p.1 • p.2 : S × B' → B') ∘ (Prod.map σ φ) =
        φ ∘ (fun p ↦ p.1 • p.2 : R × A → A) := by ext; simp
      -- Furthermore, `σ` is an open quotient map as is `φ`,
      -- so the product `σ × φ` is an open quotient map, by a result in the library.
      have hoq : IsOpenQuotientMap (_ : R × A → S × B') := IsOpenQuotientMap.prodMap hσ hφo
      -- This is the left map in the diagram. So by a standard fact about open quotient maps,
      -- to prove that the bottom map is continuous, it suffices to prove
      -- that the diagonal map is continuous.
      rw [← hoq.continuous_comp_iff]
      -- but the diagonal is the composite of the continuous maps `φ` and `• : R × A → A`
      rw [hφ2]
      -- so we're done
      exact Continuous.comp hφo.continuous hA
    · /- In this branch we show that addition is continuous for the coinduced topology on `B`.
        The argument is basically the same, this time using commutativity of
        A × A --(+)--> A
          |            |
          |φ × φ       |φ
          |            |
         \/            \/
        B × B --(+)--> B
      -/
      apply ContinuousAdd.mk
      obtain ⟨hA⟩ := IsModuleTopology.toContinuousAdd R A
      have hφ2 : (fun p ↦ p.1 + p.2 : B' × B' → B') ∘ (Prod.map φ φ) =
        φ ∘ (fun p ↦ p.1 + p.2 : A × A → A) := by ext; simp
      rw [← (IsOpenQuotientMap.prodMap hφo hφo).continuous_comp_iff, hφ2]
      exact Continuous.comp hφo.continuous hA

open Topology in
/-- A linear surjection between modules with the module topology is a quotient map.
Equivalently, the pushforward of the module topology along a surjective linear map is
again the module topology. -/
/-
**IsModuleTopology.isQuotientMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsModu
leTopology`。
形式化陈述：isQuotientMap_of_surjective [τB : TopologicalSpace B] [IsModuleTopology R 
B] {φ : A ->ₗ[R] B} (hφ : Function.Surjective φ) : IsQuotientMap φ
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isQuotientMap_of_surjectiveₛₗ`：isQuotientMap_of_surject
iveₛₗ [τB : TopologicalSpace B'] [IsModuleTopology S B'] {σ : R ->+* S} (hσ : Is
OpenQuotientMap σ) (φ : A ->ₛₗ[σ] B'…
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id

--- 原说明 ---
A linear surjection between modules with the module topology is a quotient map.
Equivalently, the pushforward of the module topology along a surjective linear m
ap is
again the module topology.
-/
theorem isQuotientMap_of_surjective [τB : TopologicalSpace B] [IsModuleTopology R B]
    {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) : IsQuotientMap φ :=
  isQuotientMap_of_surjectiveₛₗ .id φ hφ

/-- A semilinear surjection between modules with the module topology is an open quotient map. -/
/-
**IsModuleTopology.isOpenQuotientMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Is
ModuleTopology`。
形式化陈述：isOpenQuotientMap_of_surjective [TopologicalSpace B] [IsModuleTopology R B
] {φ : A ->ₗ[R] B} (hφ : Function.Surjective φ) : IsOpenQuotientMap φ
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isOpenQuotientMap_of_surjectiveₛₗ`：isOpenQuotientMap_of
_surjectiveₛₗ [TopologicalSpace B'] [IsModuleTopology S B'] {σ : R ->+* S} (hσ :
 IsOpenQuotientMap σ) (φ : A ->ₛₗ[σ] B')…
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id

--- 原说明 ---
A semilinear surjection between modules with the module topology is an open quot
ient map.
-/
theorem isOpenQuotientMap_of_surjectiveₛₗ [TopologicalSpace B'] [IsModuleTopology S B']
    {σ : R →+* S} (hσ : IsOpenQuotientMap σ) (φ : A →ₛₗ[σ] B') (hφ : Function.Surjective φ) :
    IsOpenQuotientMap φ :=
  have := toContinuousAdd R A
  AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <| isQuotientMap_of_surjectiveₛₗ hσ φ hφ

/-- A linear surjection between modules with the module topology is an open quotient map. -/
/-
**IsModuleTopology.isOpenQuotientMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Is
ModuleTopology`。
形式化陈述：isOpenQuotientMap_of_surjective [TopologicalSpace B] [IsModuleTopology R B
] {φ : A ->ₗ[R] B} (hφ : Function.Surjective φ) : IsOpenQuotientMap φ
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isOpenQuotientMap_of_surjectiveₛₗ`：isOpenQuotientMap_of
_surjectiveₛₗ [TopologicalSpace B'] [IsModuleTopology S B'] {σ : R ->+* S} (hσ :
 IsOpenQuotientMap σ) (φ : A ->ₛₗ[σ] B')…
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id

--- 原说明 ---
A linear surjection between modules with the module topology is an open quotient
 map.
-/
theorem isOpenQuotientMap_of_surjective [TopologicalSpace B] [IsModuleTopology R B]
    {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    IsOpenQuotientMap φ :=
  isOpenQuotientMap_of_surjectiveₛₗ .id φ hφ

omit [IsModuleTopology R A] in
/-- A semilinear surjection to a module with the module topology is open. -/
/-
**IsModuleTopology.isOpenMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTo
pology`。
形式化陈述：isOpenMap_of_surjective [TopologicalSpace B] [IsModuleTopology R B] [Conti
nuousAdd A] [ContinuousSMul R A] {φ : A ->ₗ[R] B} (hφ : Function.Surjective φ) :
 IsOpenMap φ
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isOpenMap_of_surjectiveₛₗ`：isOpenMap_of_surjectiveₛₗ [T
opologicalSpace B'] [IsModuleTopology S B'] [ContinuousAdd A] [ContinuousSMul R 
A] {σ : R ->+* S} (hσ : IsOpenQu…
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id

--- 原说明 ---
A semilinear surjection to a module with the module topology is open.
-/
theorem isOpenMap_of_surjectiveₛₗ [TopologicalSpace B'] [IsModuleTopology S B']
    [ContinuousAdd A] [ContinuousSMul R A]
    {σ : R →+* S} (hσ : IsOpenQuotientMap σ) (φ : A →ₛₗ[σ] B') (hφ : Function.Surjective φ) :
    IsOpenMap φ := by
  have hOpenMap :=
    letI : TopologicalSpace A := moduleTopology R A
    have : IsModuleTopology R A := ⟨rfl⟩
    isOpenQuotientMap_of_surjectiveₛₗ hσ φ hφ |>.isOpenMap
  intro U hU
  exact hOpenMap U <| moduleTopology_le R A U hU

omit [IsModuleTopology R A] in
/-- A linear surjection to a module with the module topology is open. -/
/-
**IsModuleTopology.isOpenMap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTo
pology`。
形式化陈述：isOpenMap_of_surjective [TopologicalSpace B] [IsModuleTopology R B] [Conti
nuousAdd A] [ContinuousSMul R A] {φ : A ->ₗ[R] B} (hφ : Function.Surjective φ) :
 IsOpenMap φ
参数：hφ : Function.Surjective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isOpenMap_of_surjectiveₛₗ`：isOpenMap_of_surjectiveₛₗ [T
opologicalSpace B'] [IsModuleTopology S B'] [ContinuousAdd A] [ContinuousSMul R 
A] {σ : R ->+* S} (hσ : IsOpenQu…
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id

--- 原说明 ---
A linear surjection to a module with the module topology is open.
-/
theorem isOpenMap_of_surjective [TopologicalSpace B] [IsModuleTopology R B]
    [ContinuousAdd A] [ContinuousSMul R A] {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    IsOpenMap φ :=
  isOpenMap_of_surjectiveₛₗ .id φ hφ
/-
**IsModuleTopology._root_.ModuleTopology.eq_coinduced_of_surjective** 是 Mathlib 
中的一个引理，位于命名空间 `IsModuleTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ModuleTopology.eq_coinduced_of_surjectiveₛₗ
    {σ : R →+* S} (hσ : IsOpenQuotientMap σ) (φ : A →ₛₗ[σ] B') (hφ : Function.Surjective φ) :
    moduleTopology S B' = TopologicalSpace.coinduced φ inferInstance := by
  let : TopologicalSpace B' := moduleTopology S B'
  have : IsModuleTopology S B' := ⟨rfl⟩
  exact (isQuotientMap_of_surjectiveₛₗ hσ φ hφ).eq_coinduced
/-
**IsModuleTopology._root_.ModuleTopology.eq_coinduced_of_surjective** 是 Mathlib 
中的一个引理，位于命名空间 `IsModuleTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ModuleTopology.eq_coinduced_of_surjective
    {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    moduleTopology R B = TopologicalSpace.coinduced φ inferInstance :=
  ModuleTopology.eq_coinduced_of_surjectiveₛₗ .id φ hφ
/-
**IsModuleTopology.instQuot** 是 Mathlib 中的一个实例，位于命名空间 `IsModuleTopology`。
形式化陈述：instQuot (S : Submodule R A) : IsModuleTopology R (A ⧸ S)
参数：S : Submodule R A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.toContinuousAdd`：IsModuleTopology.toContinuousAdd [Topo
logicalSpace A] [IsModuleTopology R A] : ContinuousAdd A
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `IsOpenQuotientMap.isQuotientMap`：isQuotientMap (h : IsOpenQuotientMap f)
 : IsQuotientMap f
· 使用定理 `Submodule.isOpenQuotientMap_mkQ`：isOpenQuotientMap_mkQ [ContinuousAdd M]
 : IsOpenQuotientMap S.mkQ
· 使用定理 `ModuleTopology.eq_coinduced_of_surjective`：∀ {R : Type u_1} [τR : Topolo
gicalSpace R] [inst : Ring R] {A : Type u_3} [inst_1 : AddCommGroup A]   [inst_2
 : _root_.Module R A] [inst_3 :…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance instQuot (S : Submodule R A) : IsModuleTopology R (A ⧸ S) := by
  constructor
  have := toContinuousAdd R A
  have quot := (Submodule.isOpenQuotientMap_mkQ S).isQuotientMap.eq_coinduced
  have module := ModuleTopology.eq_coinduced_of_surjective <| Submodule.mkQ_surjective S
  rw [quot, module]

end surjection

section Prod

variable {R : Type*} [TopologicalSpace R] [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

/-- The product of the module topologies for two modules over a topological ring
is the module topology. -/
/-
**IsModuleTopology.instProd** 是 Mathlib 中的一个实例，位于命名空间 `IsModuleTopology`。
形式化陈述：instProd : IsModuleTopology R (M × N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.toContinuousAdd`：IsModuleTopology.toContinuousAdd [Topo
logicalSpace A] [IsModuleTopology R A] : ContinuousAdd A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ModuleTopology.continuousAdd`：ModuleTopology.continuousAdd : @Continuous
Add A (moduleTopology R A) _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_id_iff_le`：continuous_id_iff_le {t t' : TopologicalSpace α} :
 Continuous[t, t'] id ↔ t <= t'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…

--- 原说明 ---
The product of the module topologies for two modules over a topological ring
is the module topology.
-/
instance instProd : IsModuleTopology R (M × N) := by
  constructor
  have : ContinuousAdd M := toContinuousAdd R M
  have : ContinuousAdd N := toContinuousAdd R N
  -- In this proof, `M × N` always denotes the product with its *product* topology.
  -- Addition `(M × N)² → M × N` and scalar multiplication `R × (M × N) → M × N`
  -- are continuous for the product topology (by results in the library), so the module topology
  -- on `M × N` is finer than the product topology (as it's the Inf of such topologies).
  -- It thus remains to show that the product topology is finer than the module topology.
  refine le_antisymm ?_ <| sInf_le ⟨Prod.continuousSMul, Prod.continuousAdd⟩
  -- Or equivalently, if `P` denotes `M × N` with the module topology,
  let P := M × N
  let τP : TopologicalSpace P := moduleTopology R P
  have : IsModuleTopology R P := ⟨rfl⟩
  have : ContinuousAdd P := ModuleTopology.continuousAdd R P
  -- and if `i` denotes the identity map from `M × N` to `P`
  let i : M × N → P := id
  -- then we need to show that `i` is continuous.
  rw [← continuous_id_iff_le]
  change @Continuous (M × N) P instTopologicalSpaceProd τP i
  -- But `i` can be written as (m, n) ↦ (m, 0) + (0, n)
  -- or equivalently as i₁ ∘ pr₁ + i₂ ∘ pr₂, where prᵢ are the projections,
  -- the maps i₁ and i₂ are linear inclusions M → P and N → P, and the addition is P × P → P.
  let i₁ : M →ₗ[R] P := LinearMap.inl R M N
  let i₂ : N →ₗ[R] P := LinearMap.inr R M N
  rw [show (i : M × N → P) =
       (fun abcd ↦ abcd.1 + abcd.2 : P × P → P) ∘
       (fun ab ↦ (i₁ ab.1, i₂ ab.2)) by
       ext ⟨a, b⟩ <;> aesop]
  -- and these maps are all continuous, hence `i` is too
  fun_prop

end Prod

section Pi

variable {R : Type*} [TopologicalSpace R] [Semiring R]
variable {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddCommMonoid (A i)]
  [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsModuleTopology R (A i)]

/-- The product of the module topologies for a finite family of modules over a topological ring
is the module topology. -/
/-
**IsModuleTopology.instPi** 是 Mathlib 中的一个实例，位于命名空间 `IsModuleTopology`。
形式化陈述：instPi : IsModuleTopology R (forall i, A i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `IsModuleTopology.iso`：∀ {R : Type u_1} [τR : TopologicalSpace R] [inst :
 Semiring R] {A : Type u_3} [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module
 R A] [τA …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The product of the module topologies for a finite family of modules over a topol
ogical ring
is the module topology.
-/
instance instPi : IsModuleTopology R (∀ i, A i) := by
  -- This is an easy induction on the size of the finite type, given the result
  -- for binary products above. We use a "decategorified" induction principle for finite types.
  induction ι using Finite.induction_empty_option
  · -- invariance under equivalence of the finite type we're taking the product over
    case of_equiv X Y e _ _ _ _ _ =>
    exact .iso (ContinuousLinearEquiv.piCongrLeft R A e)
  · -- empty case
    infer_instance
  · -- "inductive step" is to check for product over `Option ι` case when known for product over `ι`
    case h_option ι _ hind _ _ _ _ =>
    -- `Option ι` is a `Sum` of `ι` and `Unit`
    let e : Option ι ≃ ι ⊕ Unit := Equiv.optionEquivSumPUnit ι
    -- so suffices to check for a product of modules over `ι ⊕ Unit`
    suffices IsModuleTopology R ((i' : ι ⊕ Unit) → A (e.symm i')) from
      .iso (.piCongrLeft R A e.symm)
    -- but such a product is isomorphic to a binary product
    -- of (product over `ι`) and (product over `Unit`)
    suffices IsModuleTopology R
      (((s : ι) → A (e.symm (Sum.inl s))) × ((t : Unit) → A (e.symm (Sum.inr t)))) from
      .iso (ContinuousLinearEquiv.sumPiEquivProdPi R ι Unit _).symm
    -- The product over `ι` has the module topology by the inductive hypothesis,
    -- and the product over `Unit` is just a module which is assumed to have the module topology
    have :=
      IsModuleTopology.iso (ContinuousLinearEquiv.piUnique R (fun t ↦ A (e.symm (Sum.inr t)))).symm
    -- so the result follows from the previous lemma (binary products).
    infer_instance

end Pi

section bilinear

section semiring

variable {R : Type*} [TopologicalSpace R] [CommSemiring R]
variable {B : Type*} [AddCommMonoid B] [Module R B] [TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [TopologicalSpace C] [IsModuleTopology R C]

/--
If `n` is finite and `B`,`C` are `R`-modules with the module topology,
then any bilinear map `Rⁿ × B → C` is automatically continuous.

Note that whilst this result works for semirings, for rings this result is superseded
by `IsModuleTopology.continuous_bilinear_of_finite_left`.
-/
/-
**IsModuleTopology.continuous_bilinear_of_pi_fintype** 是 Mathlib 中的一个定理，位于命名空间 `
IsModuleTopology`。
形式化陈述：continuous_bilinear_of_pi_fintype (ι : Type*) [Finite ι] (bil : (ι -> R) -
>ₗ[R] B ->ₗ[R] C) : Continuous (fun ab => bil ab.1 ab.2 : ((ι -> R) × B -> C))
参数：ι : Type*；bil : (ι -> R) ->ₗ[R] B ->ₗ[R] C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finsupp.smul_single_one`：smul_single_one [MulZeroOneClass R] (a : α) (b 
: R) : b • single a (1 : R) = single a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsModuleTopology.toContinuousAdd`：IsModuleTopology.toContinuousAdd [Topo
logicalSpace A] [IsModuleTopology R A] : ContinuousAdd A
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2

--- 原说明 ---
If `n` is finite and `B`,`C` are `R`-modules with the module topology,
then any bilinear map `Rⁿ × B → C` is automatically continuous.

Note that whilst this result works for semirings, for rings this result is super
seded
by `IsModuleTopology.continuous_bilinear_of_finite_left`.
-/
theorem continuous_bilinear_of_pi_fintype (ι : Type*) [Finite ι]
    (bil : (ι → R) →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : ((ι → R) × B → C)) := by
  classical
  cases nonempty_fintype ι
  -- The map in question, `(f, b) ↦ bil f b`, is easily checked to be equal to
  -- `(f, b) ↦ ∑ᵢ f i • bil (single i 1) b` where `single i 1 : ι → R` sends `i` to `1` and
  -- everything else to `0`.
  have h : (fun fb ↦ bil fb.1 fb.2 : ((ι → R) × B → C)) =
      (fun fb ↦ ∑ i, ((fb.1 i) • (bil (Finsupp.single i 1) fb.2) : C)) := by
    ext ⟨f, b⟩
    nth_rw 1 [← Finset.univ_sum_single f]
    simp_rw [← Finsupp.single_eq_pi_single, map_sum, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [← Finsupp.smul_single_one]
    push_cast
    simp
  rw [h]
  -- But this map is obviously continuous, because for a fixed `i`, `bil (single i 1)` is
  -- linear and thus continuous, and scalar multiplication and finite sums are continuous
  have : ContinuousAdd C := toContinuousAdd R C
  fun_prop

end semiring

section ring

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

/--
If `A`, `B` and `C` have the module topology, and if furthermore `A` is a finite `R`-module,
then any bilinear map `A × B → C` is automatically continuous
-/
@[continuity, fun_prop]
/-
**IsModuleTopology.continuous_bilinear_of_finite_left** 是 Mathlib 中的一个定理，位于命名空间 
`IsModuleTopology`。
形式化陈述：continuous_bilinear_of_finite_left [Module.Finite R A] (bil : A ->ₗ[R] B -
>ₗ[R] C) : Continuous (fun ab => bil ab.1 ab.2 : (A × B -> C))
参数：bil : A ->ₗ[R] B ->ₗ[R] C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `Function.Surjective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Surjective f → Function.S
urjective g → Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `IsModuleTopology.isQuotientMap_of_surjective`：isQuotientMap_of_surjectiv
e [τB : TopologicalSpace B] [IsModuleTopology R B] {φ : A ->ₗ[R] B} (hφ : Functi
on.Surjective φ) : IsQuotientMap φ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsModuleTopology.continuous_bilinear_of_pi_fintype`：continuous_bilinear_
of_pi_fintype (ι : Type*) [Finite ι] (bil : (ι -> R) ->ₗ[R] B ->ₗ[R] C) : Contin
uous (fun ab => bil ab.1 ab.2 : ((ι -> R…

--- 原说明 ---
If `A`, `B` and `C` have the module topology, and if furthermore `A` is a finite
 `R`-module,
then any bilinear map `A × B → C` is automatically continuous
-/
theorem continuous_bilinear_of_finite_left [Module.Finite R A]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  -- `A` is finite and hence admits a surjection from `Rⁿ` for some finite `n`.
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R A
  -- The induced linear map `φ : Rⁿ × B → A × B` is surjective
  let bil' : (Fin m → R) →ₗ[R] B →ₗ[R] C := bil.comp f
  let φ := f.prodMap (LinearMap.id : B →ₗ[R] B)
  have hφ : Function.Surjective φ := Function.Surjective.prodMap hf fun b ↦ ⟨b, rfl⟩
  -- ... and thus a quotient map, so it suffices to prove that the composite `Rⁿ × B → C` is
  -- continuous.
  rw [Topology.IsQuotientMap.continuous_iff (isQuotientMap_of_surjective hφ)]
  -- But this follows from an earlier result.
  exact continuous_bilinear_of_pi_fintype (Fin m) bil'

/--
If `A`, `B` and `C` have the module topology, and if furthermore `B` is a finite `R`-module,
then any bilinear map `A × B → C` is automatically continuous
-/
@[continuity, fun_prop]
/-
**IsModuleTopology.continuous_bilinear_of_finite_right** 是 Mathlib 中的一个定理，位于命名空间
 `IsModuleTopology`。
形式化陈述：continuous_bilinear_of_finite_right [Module.Finite R B] (bil : A ->ₗ[R] B 
->ₗ[R] C) : Continuous (fun ab => bil ab.1 ab.2 : (A × B -> C))
参数：bil : A ->ₗ[R] B ->ₗ[R] C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `IsModuleTopology.continuous_bilinear_of_finite_left`：continuous_bilinear
_of_finite_left [Module.Finite R A] (bil : A ->ₗ[R] B ->ₗ[R] C) : Continuous (fu
n ab => bil ab.1 ab.2 : (A × B -> C))
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1

--- 原说明 ---
If `A`, `B` and `C` have the module topology, and if furthermore `B` is a finite
 `R`-module,
then any bilinear map `A × B → C` is automatically continuous
-/
theorem continuous_bilinear_of_finite_right [Module.Finite R B]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  -- We already proved this when `A` is finite instead of `B`, so it's obvious by symmetry
  rw [show (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) =
    ((fun ba ↦ bil.flip ba.1 ba.2 : (B × A → C)) ∘ (Prod.swap : A × B → B × A)) by ext; simp]
  fun_prop

end ring

end bilinear

section algebra

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D]

include R in
/-- If `D` is an `R`-algebra, finite as an `R`-module, and if `D` has the module topology,
then multiplication on `D` is automatically continuous. -/
@[continuity, fun_prop]
/-
**IsModuleTopology.continuous_mul_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleT
opology`。
形式化陈述：continuous_mul_of_finite : Continuous (fun ab => ab.1 * ab.2 : D × D -> D)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_bilinear_of_finite_left`：continuous_bilinear
_of_finite_left [Module.Finite R A] (bil : A ->ₗ[R] B ->ₗ[R] C) : Continuous (fu
n ab => bil ab.1 ab.2 : (A × B -> C))
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `D` is an `R`-algebra, finite as an `R`-module, and if `D` has the module top
ology,
then multiplication on `D` is automatically continuous.
-/
theorem continuous_mul_of_finite : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) :=
  -- Proof: multiplication is bilinear so this follows from previous results.
  continuous_bilinear_of_finite_left (LinearMap.mul R D)

include R in
/-- If `R` is a topological ring and `D` is an `R`-algebra, finite as an `R`-module,
and if `D` is given the module topology, then `D` is a topological ring. -/
/-
**IsModuleTopology.isTopologicalRing** 是 Mathlib 中的一个定理，位于命名空间 `IsModuleTopology
`。
形式化陈述：isTopologicalRing : IsTopologicalRing D where -- Proof: we have already ch
ecked all the axioms above. continuous_add
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.toContinuousAdd`：IsModuleTopology.toContinuousAdd [Topo
logicalSpace A] [IsModuleTopology R A] : ContinuousAdd A
· 使用定理 `IsModuleTopology.continuous_mul_of_finite`：continuous_mul_of_finite : Co
ntinuous (fun ab => ab.1 * ab.2 : D × D -> D)
· 使用定理 `IsModuleTopology.continuous_neg`：continuous_neg (C : Type*) [AddCommGrou
p C] [Module R C] [TopologicalSpace C] [IsModuleTopology R C] : Continuous (fun 
a => -a : C -> C)

--- 原说明 ---
If `R` is a topological ring and `D` is an `R`-algebra, finite as an `R`-module,
and if `D` is given the module topology, then `D` is a topological ring.
-/
theorem isTopologicalRing : IsTopologicalRing D where
  -- Proof: we have already checked all the axioms above.
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul_of_finite R D
  continuous_neg := continuous_neg R D

end algebra

end IsModuleTopology

