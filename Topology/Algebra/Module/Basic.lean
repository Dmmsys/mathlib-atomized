/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Theory of topological modules

We use the class `ContinuousSMul` for topological (semi) modules and topological vector spaces.
-/

@[expose] public section

assert_not_exists Cardinal TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [Module R M]

/-
**ContinuousSMul.of_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousSMul.of_nhds_zero [IsTopologicalRing R] [IsTopologicalAddGroup M
] (hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0)) (hmulleft : f
orall m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0)) (hmulright : forall a : R
, Tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : ContinuousSMul R M where continuou
s_smul
参数：hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0)；hmulleft : for
all m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0)；hmulright : forall a : R, Te
ndsto (fun m : M => a • m) (𝓝 0) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_continuousAt_zero₂`：∀ {G : Type w} [inst : TopologicalSpac
e G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {H : Type u_1} {M : Type u_
2}   [inst_3 : AddComm…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DistribSMul.toAddMonoidHom_apply`：∀ {M : Type u_1} (A : Type u_7) [inst 
: AddZeroClass A] [inst_1 : DistribSMul M A] (x : M) (x_1 : A),   (DistribSMul.t
oAddMonoidHom A x) x_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem ContinuousSMul.of_nhds_zero [IsTopologicalRing R] [IsTopologicalAddGroup M]
    (hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0))
    (hmulleft : ∀ m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0))
    (hmulright : ∀ a : R, Tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : ContinuousSMul R M where
  continuous_smul := by
    rw [← nhds_prod_eq] at hmul
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.smul : R →+ M →+ M) ?_ ?_ ?_ <;>
      simpa [ContinuousAt]

variable (R M) in
omit [TopologicalSpace R] in
/-- A topological module over a ring has continuous negation.

This cannot be an instance, because it would cause search for `[Module ?R M]` with unknown `R`. -/
/-
**ContinuousNeg.of_continuousConstSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousNeg.of_continuousConstSMul [ContinuousConstSMul R M] : Continuou
sNeg M where continuous_neg
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…

--- 原说明 ---
A topological module over a ring has continuous negation.

This cannot be an instance, because it would cause search for `[Module ?R M]` wi
th unknown `R`.
-/
theorem ContinuousNeg.of_continuousConstSMul [ContinuousConstSMul R M] : ContinuousNeg M where
  continuous_neg := by simpa using continuous_const_smul (T := M) (-1 : R)

end

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]

/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nontrivially normed field. -/
/-
**Submodule.eq_top_of_nonempty_interior'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.eq_top_of_nonempty_interior' [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
 (s : Submodule R M) (hs : (interior (s : Set M)).Nonempty) : s = ⊤
参数：𝓝[{ x : R | IsUnit x }] 0；s : Submodule R M；hs : (interior (s : Set M)).Nonem
pty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.zero_smul_const`：∀ {M : Type u_1} {X : Type u_2} {α : Typ
e u_4} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : Zer
o M] [inst_3 : Zero …
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Submodule.smul_mem_iff'`：smul_mem_iff' [Group G] [MulAction G M] [SMul G
 R] [IsScalarTower G R M] (g : G) : g • x in p ↔ x in p
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Submodule.add_mem_iff_right`：∀ {R : Type u} {M : Type v} [inst : Ring R]
 [inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   
{x y : M}, x ∈ p …

--- 原说明 ---
If `M` is a topological module over `R` and `0` is a limit of invertible element
s of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nontrivially normed field.
-/
theorem Submodule.eq_top_of_nonempty_interior' [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
    (s : Submodule R M) (hs : (interior (s : Set M)).Nonempty) : s = ⊤ := by
  rcases hs with ⟨y, hy⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [mem_interior_iff_mem_nhds] at hy
  have : Tendsto (fun c : R ↦ y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + 0)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).zero_smul_const _)
  rw [add_zero] at this
  obtain ⟨_, hu : y + _ • _ ∈ s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (Filter.mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y ∈ ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

variable (R M) [IsDomain R]

/-- Let `R` be a topological ring such that zero is not an isolated point (e.g., a nontrivially
normed field, see `NormedField.punctured_nhds_neBot`). Let `M` be a nontrivial module over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. We formulate this
using `NeBot (𝓝[≠] x)`.

This lemma is not an instance because Lean would need to find `[ContinuousSMul ?m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `Real.punctured_nhds_module_neBot`.
One can also use `haveI := Module.punctured_nhds_neBot R M` in a proof.
-/
/-
**Module.punctured_nhds_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.punctured_nhds_neBot [Nontrivial M] [NeBot (𝓝[!=] (0 : R))] [Module
.IsTorsionFree R M] (x : M) : NeBot (𝓝[!=] x)
参数：𝓝[!=] (0 : R)；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.zero_smul_const`：∀ {M : Type u_1} {X : Type u_2} {α : Typ
e u_4} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : Zer
o M] [inst_3 : Zero …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot

--- 原说明 ---
Let `R` be a topological ring such that zero is not an isolated point (e.g., a n
ontrivially
normed field, see `NormedField.punctured_nhds_neBot`). Let `M` be a nontrivial m
odule over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. 
We formulate this
using `NeBot (𝓝[≠] x)`.

This lemma is not an instance because Lean would need to find `[ContinuousSMul ?
m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `Real.punctured_n
hds_module_neBot`.
One can also use `haveI := Module.punctured_nhds_neBot R M` in a proof.
-/
theorem Module.punctured_nhds_neBot [Nontrivial M] [NeBot (𝓝[≠] (0 : R))] [Module.IsTorsionFree R M]
    (x : M) : NeBot (𝓝[≠] x) := by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices Tendsto (fun c : R => x + c • y) (𝓝[≠] 0) (𝓝[≠] x) from this.neBot
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 <| ?_)
  · convert! tendsto_const_nhds.add ((@tendsto_id R _).zero_smul_const y)
    rw [add_zero]
  · intro c hc
    simpa [hy] using hc

end

section LatticeOps

variable {R S M₁ M₂ M₂' : Type*} {φ : R → S} [SMul R M₁] [SMul R M₂] [SMul S M₂']
  [u : TopologicalSpace R] [u' : TopologicalSpace S]
  {t : TopologicalSpace M₂} {t' : TopologicalSpace M₂'}
  [ContinuousSMul R M₂] [ContinuousSMul S M₂']
  {F : Type*} [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂] (f : F)
  {F' : Type*} [FunLike F' M₁ M₂'] [MulActionSemiHomClass F' φ M₁ M₂'] (f' : F')

/-
**continuousSMul_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousSMul_inducedₛₗ`：continuousSMul_inducedₛₗ (hφ : Continuous φ) :
 @ContinuousSMul R M₁ _ u (t'.induced f')
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuousSMul_inducedₛₗ (hφ : Continuous φ) : @ContinuousSMul R M₁ _ u (t'.induced f') :=
  let _ : TopologicalSpace M₁ := t'.induced f'
  IsInducing.continuousSMul ⟨rfl⟩ hφ (map_smulₛₗ f' _ _)
/-
**continuousSMul_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousSMul_inducedₛₗ`：continuousSMul_inducedₛₗ (hφ : Continuous φ) :
 @ContinuousSMul R M₁ _ u (t'.induced f')
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f) :=
  continuousSMul_inducedₛₗ f continuous_id

end LatticeOps

/-- The span of a separable subset with respect to a separable scalar ring is again separable. -/
/-
**TopologicalSpace.IsSeparable.span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopologicalSpace.IsSeparable.span {R M : Type*} [AddCommMonoid M] [Semirin
g R] [Module R M] [TopologicalSpace M] [TopologicalSpace R] [SeparableSpace R] [
ContinuousAdd M] [ContinuousSMul R M] {s : Set M} (hs : IsSeparable s) : IsSepar
able (Submodule.span R s : Set M)
参数：hs : IsSeparable s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.span_eq_iUnion_nat`：Submodule.span_eq_iUnion_nat (s : Set M) :
 (Submodule.span R s : Set M) = ⋃ (n : Nat), (fun (f : Fin n -> (R × M)) => ∑ i,
 (f i).1 • (f i).2…
· 使用定理 `TopologicalSpace.IsSeparable.iUnion`：∀ {α : Type u} [t : TopologicalSpac
e α] {ι : Sort u_2} [Countable ι] {s : ι → Set α},   (∀ (i : ι), TopologicalSpac
e.IsSeparable (s i)) → To…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.IsSeparable.image`：∀ {α : Type u} [t : TopologicalSpace
 α] {β : Type u_2} [inst : TopologicalSpace β] {s : Set α},   TopologicalSpace.I
sSeparable s → ∀ {f : α …
· 使用引理 `TopologicalSpace.isSeparable_pi`：isSeparable_pi {ι : Type*} [Countable ι
] {α : ι -> Type*} {s : forall i, Set (α i)} [forall i, TopologicalSpace (α i)] 
(h : forall i, IsSepa…
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `TopologicalSpace.IsSeparable.prod`：∀ {α : Type u} [t : TopologicalSpace 
α] {β : Type u_2} [inst : TopologicalSpace β] {s : Set α} {t_1 : Set β},   Topol
ogicalSpace.IsSeparable…
· 使用定理 `TopologicalSpace.IsSeparable.of_separableSpace`：∀ {α : Type u} [t : Topo
logicalSpace α] [h : TopologicalSpace.SeparableSpace α] (s : Set α),   Topologic
alSpace.IsSeparable s
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
The span of a separable subset with respect to a separable scalar ring is again 
separable.
-/
lemma TopologicalSpace.IsSeparable.span {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M]
    [TopologicalSpace M] [TopologicalSpace R] [SeparableSpace R]
    [ContinuousAdd M] [ContinuousSMul R M] {s : Set M} (hs : IsSeparable s) :
    IsSeparable (Submodule.span R s : Set M) := by
  rw [Submodule.span_eq_iUnion_nat]
  refine .iUnion fun n ↦ .image ?_ ?_
  · have : IsSeparable {f : Fin n → R × M | ∀ (i : Fin n), f i ∈ Set.univ ×ˢ s} := by
      apply isSeparable_pi (fun i ↦ .prod (.of_separableSpace Set.univ) hs)
    rwa [Set.univ_prod] at this
  · apply continuous_finsetSum _ (fun i _ ↦ ?_)
    exact (continuous_fst.comp (continuous_apply i)).smul (continuous_snd.comp (continuous_apply i))

namespace Submodule

/-
**Submodule.topologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：topologicalAddGroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [
TopologicalSpace M] [IsTopologicalAddGroup M] (S : Submodule R M) : IsTopologica
lAddGroup S
参数：S : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalAddGroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (S : Submodule R M) : IsTopologicalAddGroup S :=
  inferInstanceAs (IsTopologicalAddGroup S.toAddSubgroup)

end Submodule

section closure

variable {R : Type u} {M : Type v} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousConstSMul R M]

/-
**Submodule.mapsTo_smul_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.mapsTo_smul_closure (s : Submodule R M) (c : R) : Set.MapsTo (c 
• ·) (closure s : Set M) (closure s)
参数：s : Submodule R M；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem Submodule.mapsTo_smul_closure (s : Submodule R M) (c : R) :
    Set.MapsTo (c • ·) (closure s : Set M) (closure s) :=
  have : Set.MapsTo (c • ·) (s : Set M) s := fun _ h ↦ s.smul_mem c h
  this.closure (continuous_const_smul c)
/-
**Submodule.smul_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.smul_closure_subset (s : Submodule R M) (c : R) : c • closure (s
 : Set M) subseteq closure (s : Set M)
参数：s : Submodule R M；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Submodule.mapsTo_smul_closure`：Submodule.mapsTo_smul_closure (s : Submod
ule R M) (c : R) : Set.MapsTo (c • ·) (closure s : Set M) (closure s)
-/
theorem Submodule.smul_closure_subset (s : Submodule R M) (c : R) :
    c • closure (s : Set M) ⊆ closure (s : Set M) :=
  (s.mapsTo_smul_closure c).image_subset

variable [ContinuousAdd M]

/-- The (topological-space) closure of a submodule of a topological `R`-module `M` is itself
a submodule. -/
/-
**Submodule.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.topologicalClosure (s : Submodule R M) : Submodule R M
参数：s : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mapsTo_smul_closure`：Submodule.mapsTo_smul_closure (s : Submod
ule R M) (c : R) : Set.MapsTo (c • ·) (closure s : Set M) (closure s)

--- 原说明 ---
The (topological-space) closure of a submodule of a topological `R`-module `M` i
s itself
a submodule.
-/
def Submodule.topologicalClosure (s : Submodule R M) : Submodule R M :=
  { s.toAddSubmonoid.topologicalClosure with
    smul_mem' := s.mapsTo_smul_closure }

@[simp, norm_cast]
/-
**Submodule.topologicalClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.topologicalClosure_coe (s : Submodule R M) : (s.topologicalClosu
re : Set M) = closure (s : Set M)
参数：s : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Submodule.topologicalClosure_coe (s : Submodule R M) :
    (s.topologicalClosure : Set M) = closure (s : Set M) :=
  rfl
/-
**Submodule.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.le_topologicalClosure (s : Submodule R M) : s <= s.topologicalCl
osure
参数：s : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Submodule.le_topologicalClosure (s : Submodule R M) : s ≤ s.topologicalClosure :=
  subset_closure
/-
**Submodule.closure_subset_topologicalClosure_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.closure_subset_topologicalClosure_span (s : Set M) : closure s s
ubseteq (span R s).topologicalClosure
参数：s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.topologicalClosure_coe`：Submodule.topologicalClosure_coe (s : 
Submodule R M) : (s.topologicalClosure : Set M) = closure (s : Set M)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem Submodule.closure_subset_topologicalClosure_span (s : Set M) :
    closure s ⊆ (span R s).topologicalClosure := by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono subset_span
/-
**Submodule.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isClosed_topologicalClosure (s : Submodule R M) : IsClosed (s.to
pologicalClosure : Set M)
参数：s : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Submodule.isClosed_topologicalClosure (s : Submodule R M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure
/-
**Submodule.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.topologicalClosure_minimal (s : Submodule R M) {t : Submodule R 
M} (h : s <= t) (ht : IsClosed (t : Set M)) : s.topologicalClosure <= t
参数：s : Submodule R M；h : s <= t；ht : IsClosed (t : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Submodule.topologicalClosure_minimal (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**Submodule.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.topologicalClosure_mono {s : Submodule R M} {t : Submodule R M} 
(h : s <= t) : s.topologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem Submodule.topologicalClosure_mono {s : Submodule R M} {t : Submodule R M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  closure_mono h

/-- The topological closure of a closed submodule `s` is equal to `s`. -/
/-
**IsClosed.submodule_topologicalClosure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.submodule_topologicalClosure_eq {s : Submodule R M} (hs : IsClose
d (s : Set M)) : s.topologicalClosure = s
参数：hs : IsClosed (s : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
The topological closure of a closed submodule `s` is equal to `s`.
-/
theorem IsClosed.submodule_topologicalClosure_eq {s : Submodule R M} (hs : IsClosed (s : Set M)) :
    s.topologicalClosure = s :=
  SetLike.ext' hs.closure_eq

/-- A subspace is dense iff its topological closure is the entire space. -/
/-
**Submodule.dense_iff_topologicalClosure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.dense_iff_topologicalClosure_eq_top {s : Submodule R M} : Dense 
(s : Set M) ↔ s.topologicalClosure = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A subspace is dense iff its topological closure is the entire space.
-/
theorem Submodule.dense_iff_topologicalClosure_eq_top {s : Submodule R M} :
    Dense (s : Set M) ↔ s.topologicalClosure = ⊤ := by
  rw [← SetLike.coe_set_eq, dense_iff_closure_eq]
  simp
/-
**Submodule.topologicalClosure.completeSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.topologicalClosure.completeSpace {M' : Type*} [AddCommMonoid M']
 [Module R M'] [UniformSpace M'] [ContinuousAdd M'] [ContinuousConstSMul R M'] [
CompleteSpace M'] (U : Submodule R M') : CompleteSpace U.topologicalClosure
参数：U : Submodule R M'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
instance Submodule.topologicalClosure.completeSpace {M' : Type*} [AddCommMonoid M'] [Module R M']
    [UniformSpace M'] [ContinuousAdd M'] [ContinuousConstSMul R M'] [CompleteSpace M']
    (U : Submodule R M') : CompleteSpace U.topologicalClosure :=
  isClosed_closure.completeSpace_coe

/-- A maximal proper subspace of a topological module (i.e a `Submodule` satisfying `IsCoatom`)
is either closed or dense. -/
/-
**Submodule.isClosed_or_dense_of_isCoatom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isClosed_or_dense_of_isCoatom (s : Submodule R M) (hs : IsCoatom
 s) : IsClosed (s : Set M) ∨ Dense (s : Set M)
参数：s : Submodule R M；hs : IsCoatom s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.dense_iff_topologicalClosure_eq_top`：Submodule.dense_iff_topol
ogicalClosure_eq_top {s : Submodule R M} : Dense (s : Set M) ↔ s.topologicalClos
ure = ⊤
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCoatom.le_iff`：IsCoatom.le_iff (h : IsCoatom a) : a <= x ↔ x = ⊤ ∨ x =
 a
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure

--- 原说明 ---
A maximal proper subspace of a topological module (i.e a `Submodule` satisfying 
`IsCoatom`)
is either closed or dense.
-/
theorem Submodule.isClosed_or_dense_of_isCoatom (s : Submodule R M) (hs : IsCoatom s) :
    IsClosed (s : Set M) ∨ Dense (s : Set M) := by
  refine (hs.le_iff.mp s.le_topologicalClosure).symm.imp ?_ dense_iff_topologicalClosure_eq_top.mpr
  exact fun h ↦ h ▸ isClosed_closure

end closure

section CompleteSpace

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [Semiring R] [AddCommMonoid M] [UniformSpace M] [Module R M]
    [CompleteSpace M] (K : Submodule R M) [c : IsClosed (K : Set M)] : CompleteSpace K :=
  IsComplete.completeSpace_coe (c.isComplete)

end CompleteSpace

namespace Submodule

variable {ι R : Type*} {M : ι → Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, TopologicalSpace (M i)] [DecidableEq ι]

/-- If `s i` is a family of submodules, each is in its module,
then the closure of their span in the indexed product of the modules
is the product of their closures.

In case of a finite index type, this statement immediately follows from `Submodule.iSup_map_single`.
However, the statement is true for an infinite index type as well. -/
/-
**Submodule.closure_coe_iSup_map_single** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：closure_coe_iSup_map_single (s : forall i, Submodule R (M i)) : closure (↑
(⨆ i, (s i).map (LinearMap.single R M i)) : Set (forall i, M i)) = Set.univ.pi f
un i => closure (s i)
参数：s : forall i, Submodule R (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_pi_set`：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) 
= pi…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.iSup_map_single_le`：iSup_map_single_le [DecidableEq ι] : ⨆ i, 
map (LinearMap.single R φ i) (p i) <= pi I p
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_pi_iff`：isOpen_pi_iff {s : Set (forall a, A a)} : IsOpen s ↔ fora
ll f, f in s -> exists (I : Finset ι) (u : forall a, Set (A a)), (forall a, a in
 I …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
If `s i` is a family of submodules, each is in its module,
then the closure of their span in the indexed product of the modules
is the product of their closures.

In case of a finite index type, this statement immediately follows from `Submodu
le.iSup_map_single`.
However, the statement is true for an infinite index type as well.
-/
theorem closure_coe_iSup_map_single (s : ∀ i, Submodule R (M i)) :
    closure (↑(⨆ i, (s i).map (LinearMap.single R M i)) : Set (∀ i, M i)) =
      Set.univ.pi fun i ↦ closure (s i) := by
  rw [← closure_pi_set]
  refine (closure_mono ?_).antisymm <| closure_minimal ?_ isClosed_closure
  · exact SetLike.coe_mono <| iSup_map_single_le
  · simp only [Set.subset_def, mem_closure_iff]
    intro x hx U hU hxU
    rcases isOpen_pi_iff.mp hU x hxU with ⟨t, V, hV, hVU⟩
    refine ⟨∑ i ∈ t, Pi.single i (x i), hVU ?_, ?_⟩
    · simp_all [Finset.sum_pi_single]
    · exact sum_mem fun i hi ↦ mem_iSup_of_mem i <| mem_map_of_mem <| hx _ <| Set.mem_univ _

/-- If `s i` is a family of submodules, each is in its module,
then the closure of their span in the indexed product of the modules
is the product of their closures.

In case of a finite index type, this statement immediately follows from `Submodule.iSup_map_single`.
However, the statement is true for an infinite index type as well.

This version is stated in terms of `Submodule.topologicalClosure`,
thus assumes that `M i`s are topological modules over `R`.
However, the statement is true without assuming continuity of the operations,
see `Submodule.closure_coe_iSup_map_single` above. -/
/-
**Submodule.topologicalClosure_iSup_map_single** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：topologicalClosure_iSup_map_single [forall i, ContinuousAdd (M i)] [forall
 i, ContinuousConstSMul R (M i)] (s : forall i, Submodule R (M i)) : topological
Closure (⨆ i, (s i).map (LinearMap.single R M i)) = pi Set.univ fun i => (s i).t
opologicalClosure
参数：M i；M i；s : forall i, Submodule R (M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `instContinuousConstSMulForall`：∀ {M : Type u_1} {ι : Type u_4} {γ : ι → 
Type u_5} [inst : (i : ι) → TopologicalSpace (γ i)]   [inst_1 : (i : ι) → SMul M
 (γ i)] [∀ (i : ι),…
· 使用定理 `Pi.continuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : (i : ι) → 
TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), ContinuousA
dd (C …
· 使用定理 `Submodule.closure_coe_iSup_map_single`：closure_coe_iSup_map_single (s : 
forall i, Submodule R (M i)) : closure (↑(⨆ i, (s i).map (LinearMap.single R M i
)) : Set (forall i, M i)) =…

--- 原说明 ---
If `s i` is a family of submodules, each is in its module,
then the closure of their span in the indexed product of the modules
is the product of their closures.

In case of a finite index type, this statement immediately follows from `Submodu
le.iSup_map_single`.
However, the statement is true for an infinite index type as well.

This version is stated in terms of `Submodule.topologicalClosure`,
thus assumes that `M i`s are topological modules over `R`.
However, the statement is true without assuming continuity of the operations,
see `Submodule.closure_coe_iSup_map_single` above.
-/
theorem topologicalClosure_iSup_map_single [∀ i, ContinuousAdd (M i)]
    [∀ i, ContinuousConstSMul R (M i)] (s : ∀ i, Submodule R (M i)) :
    topologicalClosure (⨆ i, (s i).map (LinearMap.single R M i)) =
      pi Set.univ fun i ↦ (s i).topologicalClosure :=
  SetLike.coe_injective <| closure_coe_iSup_map_single _

end Submodule

section Pi

/-
**LinearMap.continuous_on_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_on_pi {ι : Type*} {R : Type*} {M : Type*} [Finite ι] 
[Semiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpa
ce M] [ContinuousAdd M] [ContinuousSMul R M] (f : (ι -> R) ->ₗ[R] M) : Continuou
s f
参数：f : (ι -> R) ->ₗ[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.pi_apply_eq_sum_univ`：pi_apply_eq_sum_univ [Fintype ι] (f : (ι
 -> R) ->ₗ[R] M₂) (x : ι -> R) : f x = ∑ i, x i • f fun j => if i = j then 1 els
e 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem LinearMap.continuous_on_pi {ι : Type*} {R : Type*} {M : Type*} [Finite ι] [Semiring R]
    [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (f : (ι → R) →ₗ[R] M) : Continuous f := by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι → R) → M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    fun_prop

end Pi

section PointwiseLimits

variable {M₁ M₂ α R S : Type*} [TopologicalSpace M₂] [T2Space M₂] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module S M₂] [ContinuousConstSMul S M₂]

variable [ContinuousAdd M₂] {σ : R →+* S} {l : Filter α}

/-- Constructs a bundled linear map from a function and a proof that this function belongs to the
closure of the set of linear maps. -/
@[simps -fullyApplied]
/-
**linearMapOfMemClosureRangeCoe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：linearMapOfMemClosureRangeCoe (f : M₁ -> M₂) (hf : f in closure (Set.range
 ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂))) : M₁ ->ₛₗ[σ] M₂
参数：f : M₁ -> M₂；hf : f in closure (Set.range ((↑) : (M₁ ->ₛₗ[σ] M₂) -> M₁ -> M₂)
)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a bundled linear map from a function and a proof that this function b
elongs to the
closure of the set of linear maps.
-/
def linearMapOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (Set.range ((↑) : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂))) : M₁ →ₛₗ[σ] M₂ :=
  { addMonoidHomOfMemClosureRangeCoe f hf with
    map_smul' := (isClosed_setOfPred_map_smul M₁ M₂ σ).closure_subset_iff.2
      (Set.range_subset_iff.2 map_smulₛₗ) hf }

/-- Construct a bundled linear map from a pointwise limit of linear maps -/
@[simps! -fullyApplied]
/-
**linearMapOfTendsto** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：linearMapOfTendsto (f : M₁ -> M₂) (g : α -> M₁ ->ₛₗ[σ] M₂) [l.NeBot] (h : 
Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ ->ₛₗ[σ] M₂
参数：f : M₁ -> M₂；g : α -> M₁ ->ₛₗ[σ] M₂；h : Tendsto (fun a x => g a x) l (𝓝 f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled linear map from a pointwise limit of linear maps
-/
def linearMapOfTendsto (f : M₁ → M₂) (g : α → M₁ →ₛₗ[σ] M₂) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₛₗ[σ] M₂ :=
  linearMapOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => Set.mem_range_self _

variable (M₁ M₂ σ)
/-
**LinearMap.isClosed_range_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ ->ₛₗ[σ] M₂) 
-> M₁ -> M₂))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
-/
theorem LinearMap.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩

end PointwiseLimits

section Quotient

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (S : Submodule R M)

/-
**Submodule._root_.QuotientModule.Quotient.topologicalSpace** 是 Mathlib 中的一个实例，位
于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.QuotientModule.Quotient.topologicalSpace : TopologicalSpace (M ⧸ S) :=
  inferInstanceAs (TopologicalSpace (Quotient S.quotientRel))
/-
**Submodule.isOpenMap_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOpenMap_mkQ [ContinuousAdd M] : IsOpenMap S.mkQ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.isOpenMap_coe`：∀ {G : Type u_1} [inst : TopologicalSpac
e G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] {N : AddSubgroup G},   Is
OpenMap QuotientAddG…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
-/
theorem isOpenMap_mkQ [ContinuousAdd M] : IsOpenMap S.mkQ :=
  QuotientAddGroup.isOpenMap_coe
/-
**Submodule.isOpenQuotientMap_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOpenQuotientMap_mkQ [ContinuousAdd M] : IsOpenQuotientMap S.mkQ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.isOpenQuotientMap_mk`：∀ {G : Type u_1} [inst : Topologi
calSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] {N : AddSubgroup G
},   IsOpenQuotientMap Quot…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
-/
theorem isOpenQuotientMap_mkQ [ContinuousAdd M] : IsOpenQuotientMap S.mkQ :=
  QuotientAddGroup.isOpenQuotientMap_mk
/-
**Submodule.isQuotientMap_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isQuotientMap_mkQ : IsQuotientMap S.mkQ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem isQuotientMap_mkQ : IsQuotientMap S.mkQ := isQuotientMap_quot_mk

@[continuity, fun_prop]
/-
**Submodule.continuous_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：continuous_mkQ : Continuous S.mkQ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
-/
theorem continuous_mkQ : Continuous S.mkQ := continuous_quot_mk
/-
**Submodule.topologicalAddGroup_quotient** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：topologicalAddGroup_quotient [IsTopologicalAddGroup M] : IsTopologicalAddG
roup (M ⧸ S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalAddGroup_quotient [IsTopologicalAddGroup M] : IsTopologicalAddGroup (M ⧸ S) :=
  inferInstanceAs <| IsTopologicalAddGroup (M ⧸ S.toAddSubgroup)
/-
**Submodule.continuousSMul_quotient** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：continuousSMul_quotient [TopologicalSpace R] [IsTopologicalAddGroup M] [Co
ntinuousSMul R M] : ContinuousSMul R (M ⧸ S) where continuous_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenQuotientMap.continuous_comp_iff`：continuous_comp_iff (h : IsOpenQu
otientMap f) {g : Y -> Z} : Continuous (g ∘ f) ↔ Continuous g
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `IsOpenQuotientMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOp
enQuotientMap id
· 使用定理 `Submodule.isOpenQuotientMap_mkQ`：isOpenQuotientMap_mkQ [ContinuousAdd M]
 : IsOpenQuotientMap S.mkQ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
-/
instance continuousSMul_quotient [TopologicalSpace R] [IsTopologicalAddGroup M]
    [ContinuousSMul R M] : ContinuousSMul R (M ⧸ S) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact continuous_quot_mk.comp continuous_smul
/-
**Submodule.t3_quotient_of_isClosed** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：t3_quotient_of_isClosed [IsTopologicalAddGroup M] [IsClosed (S : Set M)] :
 T3Space (M ⧸ S)
参数：S : Set M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.instT3Space`：∀ {G : Type u_1} [inst : TopologicalSpace 
G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (N : AddSubgroup G)   [N.Norm
al] [hN : IsClosed…
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
-/
instance t3_quotient_of_isClosed [IsTopologicalAddGroup M] [IsClosed (S : Set M)] :
    T3Space (M ⧸ S) :=
  letI : IsClosed (S.toAddSubgroup : Set M) := ‹_›
  QuotientAddGroup.instT3Space S.toAddSubgroup

end Submodule

end Quotient

