/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.Engel
public import Mathlib.Algebra.Lie.Normalizer
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Engel subalgebras

This file defines Engel subalgebras of a Lie algebra and provides basic related properties.

The Engel subalgebra `LieSubalgebra.Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

## Main results

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent (TODO), hence Cartan subalgebras.

* `LieSubalgebra.normalizer_eq_self_of_engel_le`:
  Lie subalgebras containing an Engel subalgebra are self-normalizing,
  provided the ambient Lie algebra is Artinian.
* `LieSubalgebra.isNilpotent_of_forall_le_engel`:
  A Lie subalgebra of a Noetherian Lie algebra is nilpotent
  if it is contained in the Engel subalgebra of all its elements.
-/

@[expose] public section

open LieAlgebra LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubalgebra

variable (R)

/-- The Engel subalgebra `Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent, hence Cartan subalgebras. -/
@[simps!]
/-
**LieSubalgebra.engel** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：engel (x : L) : LieSubalgebra R L
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Engel subalgebra `Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent, hence Cartan subalgebras.
-/
def engel (x : L) : LieSubalgebra R L :=
  { (ad R L x).maxGenEigenspace 0 with
    lie_mem' := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Module.End.mem_maxGenEigenspace, zero_smul,
        sub_zero, forall_exists_index]
      intro y z m hm n hn
      refine ⟨m + n, ?_⟩
      rw [ad_pow_lie]
      apply Finset.sum_eq_zero
      intro ij hij
      obtain (h | h) : m ≤ ij.1 ∨ n ≤ ij.2 := by rw [Finset.mem_antidiagonal] at hij; lia
      all_goals simp [Module.End.pow_map_zero_of_le h, hm, hn] }
/-
**LieSubalgebra.mem_engel_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_engel_iff (x y : L) : y in engel R x ↔ exists n : Nat, ((ad R L x) ^ n
) y = 0
参数：x y : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.End.mem_maxGenEigenspace`：mem_maxGenEigenspace (f : End R M) (μ :
 R) (m : M) : m in f.maxGenEigenspace μ ↔ exists k : Nat, ((f - μ • (1 : End R M
)) ^ k) m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_engel_iff (x y : L) :
    y ∈ engel R x ↔ ∃ n : ℕ, ((ad R L x) ^ n) y = 0 :=
  (Module.End.mem_maxGenEigenspace _ _ _).trans <| by simp only [zero_smul, sub_zero]
/-
**LieSubalgebra.self_mem_engel** 是 Mathlib 中的一个引理，位于命名空间 `LieSubalgebra`。
形式化陈述：self_mem_engel (x : L) : x in engel R x
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `lie_self`：lie_self : ⁅x, x⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma self_mem_engel (x : L) : x ∈ engel R x := by
  simp only [mem_engel_iff]
  exact ⟨1, by simp⟩

@[simp]
/-
**LieSubalgebra.engel_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieSubalgebra`。
形式化陈述：engel_zero : engel R (0 : L) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `LieSubalgebra.mem_engel_iff`：mem_engel_iff (x y : L) : y in engel R x ↔ 
exists n : Nat, ((ad R L x) ^ n) y = 0
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
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma engel_zero : engel R (0 : L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [mem_engel_iff, map_zero]
  use 1
  simp only [pow_one, LinearMap.zero_apply]

/-- Engel subalgebras are self-normalizing.
See `LieSubalgebra.normalizer_eq_self_of_engel_le` for a proof that Lie-subalgebras
containing an Engel subalgebra are also self-normalizing,
provided that the ambient Lie algebra is Artinian. -/
@[simp]
/-
**LieSubalgebra.normalizer_engel** 是 Mathlib 中的一个引理，位于命名空间 `LieSubalgebra`。
形式化陈述：normalizer_engel (x : L) : normalizer (engel R x) = engel R x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieSubalgebra.mem_engel_iff`：mem_engel_iff (x y : L) : y in engel R x ↔ 
exists n : Nat, ((ad R L x) ^ n) y = 0
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `LieSubalgebra.mem_normalizer_iff`：mem_normalizer_iff (x : L) : x in H.no
rmalizer ↔ forall y : L, y in H -> ⁅x, y⁆ in H
· 使用引理 `LieSubalgebra.self_mem_engel`：self_mem_engel (x : L) : x in engel R x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `LieSubalgebra.le_normalizer`：le_normalizer : H <= H.normalizer

--- 原说明 ---
Engel subalgebras are self-normalizing.
See `LieSubalgebra.normalizer_eq_self_of_engel_le` for a proof that Lie-subalgeb
ras
containing an Engel subalgebra are also self-normalizing,
provided that the ambient Lie algebra is Artinian.
-/
lemma normalizer_engel (x : L) : normalizer (engel R x) = engel R x := by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (self_mem_engel R x)
  rw [← lie_skew, neg_mem_iff (G := L), mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [mem_engel_iff]
  use n + 1
  rw [pow_succ, Module.End.mul_apply]
  exact hn

variable {R}

open Filter in
/-- A Lie-subalgebra of an Artinian Lie algebra is self-normalizing
if it contains an Engel subalgebra.
See `LieSubalgebra.normalizer_engel` for a proof that Engel subalgebras are self-normalizing,
avoiding the Artinian condition. -/
/-
**LieSubalgebra.normalizer_eq_self_of_engel_le** 是 Mathlib 中的一个引理，位于命名空间 `LieSub
algebra`。
形式化陈述：normalizer_eq_self_of_engel_le [IsArtinian R L] (H : LieSubalgebra R L) (x
 : L) (h : engel R x <= H) : normalizer H = H
参数：H : LieSubalgebra R L；x : L；h : engel R x <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieSubalgebra.mem_normalizer_iff`：mem_normalizer_iff (x : L) : x in H.no
rmalizer ↔ forall y : L, y in H -> ⁅x, y⁆ in H
· 使用引理 `LieSubalgebra.self_mem_engel`：self_mem_engel (x : L) : x in engel R x
· 使用定理 `LieSubalgebra.le_normalizer`：le_normalizer : H <= H.normalizer
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearMap.eventually_codisjoint_ker_pow_range_pow`：eventually_codisjoint
_ker_pow_range_pow (f : Module.End R M) : forallᶠ n in atTop, Codisjoint (Linear
Map.ker (f ^ n)) (LinearMap.range (f ^ …
· 使用定理 `LieSubalgebra.instIsArtinianSubtypeMem`：∀ (R : Type u) (L : Type v) [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgeb
ra R L)   [IsArtinian R L], …
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `AddSubmonoid.mk_eq_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] (S : A
ddSubmonoid M) {a : M} {ha : a ∈ S}, ⟨a, ha⟩ = 0 ↔ a = 0
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b

--- 原说明 ---
A Lie-subalgebra of an Artinian Lie algebra is self-normalizing
if it contains an Engel subalgebra.
See `LieSubalgebra.normalizer_engel` for a proof that Engel subalgebras are self
-normalizing,
avoiding the Artinian condition.
-/
lemma normalizer_eq_self_of_engel_le [IsArtinian R L]
    (H : LieSubalgebra R L) (x : L) (h : engel R x ≤ H) :
    normalizer H = H := by
  set N := normalizer H
  apply le_antisymm _ (le_normalizer H)
  calc N.toSubmodule ≤ (engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : ∀ n ∈ N, ⁅x, n⁆ ∈ H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (self_mem_engel R x))
    rwa [← lie_skew, neg_mem_iff (G := L)]
  have aux₂ : ∀ n ∈ N, ⁅x, n⁆ ∈ N := fun n hn ↦ le_normalizer H (aux₁ _ hn)
  let dx : N →ₗ[R] N := (ad R L x).restrict aux₂
  obtain ⟨k, hk⟩ : ∃ a, ∀ b ≥ a, Codisjoint (LinearMap.ker (dx ^ b)) (LinearMap.range (dx ^ b)) :=
    eventually_atTop.mp <| dx.eventually_codisjoint_ker_pow_range_pow
  specialize hk (k + 1) (Nat.le_add_right k 1)
  rw [← Submodule.map_subtype_top N.toSubmodule, Submodule.map_le_iff_le_comap]
  apply hk
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_left
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    simp only [Submodule.mem_comap, mem_engel_iff, mem_toSubmodule]
    use k + 1
    clear hk; revert hy
    generalize k + 1 = k
    induction k generalizing y with
    | zero =>
      cases y; intro hy; simp only [pow_zero, Module.End.one_apply]
      exact (AddSubmonoid.mk_eq_zero N.toAddSubmonoid).mp hy
    | succ k ih => solve_by_elim
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_right
    rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨y, rfl⟩
    simp only [pow_succ', Module.End.mul_apply, Submodule.mem_comap, mem_toSubmodule]
    apply aux₁
    simp only [Submodule.coe_subtype, SetLike.coe_mem]

set_option backward.isDefEq.respectTransparency.types false in
/-- A Lie subalgebra of a Noetherian Lie algebra is nilpotent
if it is contained in the Engel subalgebra of all its elements. -/
/-
**LieSubalgebra.isNilpotent_of_forall_le_engel** 是 Mathlib 中的一个引理，位于命名空间 `LieSub
algebra`。
形式化陈述：isNilpotent_of_forall_le_engel [IsNoetherian R L] (H : LieSubalgebra R L) 
(h : forall x in H, H <= engel R x) : LieRing.IsNilpotent H
参数：H : LieSubalgebra R L；h : forall x in H, H <= engel R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.isNilpotent_iff_forall`：LieAlgebra.isNilpotent_iff_forall [Is
Noetherian R L] : LieRing.IsNilpotent L ↔ forall x, IsNilpotent LieAlgebra.ad R 
L x
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Module.End.pow_map_zero_of_le`：pow_map_zero_of_le {f : End R M} {m : M} 
{k l : Nat} (hk : k <= l) (hm : (f ^ k) m = 0) : (f ^ l) m = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_stabilizes_iff_noetherian`：monotone_stabilizes_iff_noetherian :
 (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ I
sNoetherian R M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `LieSubalgebra.coe_ad_pow`：LieSubalgebra.coe_ad_pow (H : LieSubalgebra R 
L) (x y : H) (n : Nat) : ((ad R H x ^ n) y : L) = (ad R L x ^ n) y
· 使用引理 `LieSubalgebra.mem_engel_iff`：mem_engel_iff (x y : L) : y in engel R x ↔ 
exists n : Nat, ((ad R L x) ^ n) y = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A Lie subalgebra of a Noetherian Lie algebra is nilpotent
if it is contained in the Engel subalgebra of all its elements.
-/
lemma isNilpotent_of_forall_le_engel [IsNoetherian R L]
    (H : LieSubalgebra R L) (h : ∀ x ∈ H, H ≤ engel R x) :
    LieRing.IsNilpotent H := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := R)]
  intro x
  let K : ℕ →o Submodule R H :=
    ⟨fun n ↦ LinearMap.ker ((ad R H x) ^ n), fun m n hmn ↦ ?mono⟩
  case mono =>
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact Module.End.pow_map_zero_of_le hmn hy
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  use n
  ext y
  rw [coe_ad_pow]
  specialize h x x.2 y.2
  rw [mem_engel_iff] at h
  obtain ⟨m, hm⟩ := h
  obtain (hmn | hmn) : m ≤ n ∨ n ≤ m := le_total m n
  · exact Module.End.pow_map_zero_of_le hmn hm
  · have : ∀ k : ℕ, ((ad R L) x ^ k) y = 0 ↔ y ∈ K k := by simp [K, Subtype.ext_iff, coe_ad_pow]
    rwa [this, ← hn m hmn, ← this] at hm

end LieSubalgebra

