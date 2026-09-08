/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Quotients of seminormed groups

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M`, we provide a
`SeminormedAddCommGroup`, the group quotient `M ⧸ S`.
If `S` is closed, we provide `NormedAddCommGroup (M ⧸ S)` (regardless of whether `M` itself is
separated). The two main properties of these structures are the underlying topology is the quotient
topology and the projection is a normed group homomorphism which is norm non-increasing
(better, it has operator norm exactly one unless `S` is dense in `M`). The corresponding
universal property is that every normed group hom defined on `M` which vanishes on `S` descends
to a normed group hom defined on `M ⧸ S`.

This file also introduces a predicate `IsQuotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.

In addition, this file also provides normed structures for quotients of modules by submodules, and
of (commutative) rings by ideals. The `SeminormedAddCommGroup` and `NormedAddCommGroup`
instances described above are transferred directly, but we also define instances of `NormedSpace`,
`SeminormedCommRing`, `NormedCommRing` and `NormedAlgebra` under appropriate type class
assumptions on the original space. Moreover, while `QuotientAddGroup.completeSpace_right` works
out-of-the-box for quotients of `NormedAddCommGroup`s by `AddSubgroup`s, we need to transfer
this instance in `Submodule.Quotient.completeSpace` so that it applies to these other quotients.

## Main definitions


We use `M` and `N` to denote seminormed groups and `S : AddSubgroup M`.
All the following definitions are in the `AddSubgroup` namespace. Hence we can access
`AddSubgroup.normedMk S` as `S.normedMk`.

* `seminormedAddCommGroupQuotient` : The seminormed group structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedAddCommGroupQuotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedMk S` : the normed group hom from `M` to `M ⧸ S`.

* `lift S f hf`: implements the universal property of `M ⧸ S`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : NormedAddGroupHom (M ⧸ S) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `IsQuotient.norm_lift`: Provided `f : normed_hom M N` satisfies `IsQuotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M` we define a norm on `M ⧸ S` by
`‖x‖ = sInf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `M ⧸ S` is automatically a topological space (as any quotient of a topological space),
one needs to be careful while defining the `SeminormedAddCommGroup` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhds_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ‖x‖ < ε}` for positive `ε`.

Once this mathematical point is settled, we have two topologies that are propositionally equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `SeminormedAddCommGroup` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `IsTopologicalAddGroup.rightUniformSpace`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/

@[expose] public section


noncomputable section

open Metric Set Topology NNReal

namespace QuotientGroup
variable {M : Type*} [SeminormedCommGroup M] {S T : Subgroup M} {x : M ⧸ S} {m : M} {r ε : ℝ}

@[to_additive add_norm_aux]
/-
**QuotientGroup.norm_aux** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma norm_aux (x : M ⧸ S) : {m : M | (m : M ⧸ S) = x}.Nonempty := Quot.exists_rep x

/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x * M`. -/
@[to_additive
/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x + S`. -/]
/-
**QuotientGroup.groupSeminorm** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：groupSeminorm : GroupSeminorm (M ⧸ S) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def groupSeminorm : GroupSeminorm (M ⧸ S) where
  toFun x := infDist 1 {m : M | (m : M ⧸ S) = x}
  map_one' := infDist_zero_of_mem (by simp)
  mul_le' x y := by
    simp only [infDist_eq_iInf]
    have := (norm_aux x).to_subtype
    have := (norm_aux y).to_subtype
    refine le_ciInf_add_ciInf ?_
    rintro ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ciInf_le_of_le ⟨0, forall_mem_range.2 fun _ ↦ dist_nonneg⟩ ⟨a * b, rfl⟩ ?_
    simpa using norm_mul_le' _ _
  inv' x := eq_of_forall_le_iff fun r ↦ by
    simp only [le_infDist (norm_aux _)]
    exact (Equiv.inv _).forall_congr (by simp [← inv_eq_iff_eq_inv])

/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x * S`. -/
@[to_additive
/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x + S`. -/]
/-
**QuotientGroup.instNorm** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：instNorm : Norm (M ⧸ S) where norm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNorm : Norm (M ⧸ S) where norm := groupSeminorm

@[to_additive]
/-
**QuotientGroup.norm_eq_groupSeminorm** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：norm_eq_groupSeminorm (x : M ⧸ S) : ‖x‖ = groupSeminorm x
参数：x : M ⧸ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_eq_groupSeminorm (x : M ⧸ S) : ‖x‖ = groupSeminorm x := rfl

@[to_additive]
/-
**QuotientGroup.norm_eq_infDist** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：norm_eq_infDist (x : M ⧸ S) : ‖x‖ = infDist 1 {m : M | (m : M ⧸ S) = x}
参数：x : M ⧸ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_eq_infDist (x : M ⧸ S) : ‖x‖ = infDist 1 {m : M | (m : M ⧸ S) = x} := rfl

@[to_additive]
/-
**QuotientGroup.le_norm_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：le_norm_iff : r <= ‖x‖ ↔ forall m : M, ↑m = x -> r <= ‖m‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.le_infDist`：le_infDist {r : Real} (hs : s.Nonempty) : r <= infDis
t x s ↔ forall ⦃y⦄, y in s -> r <= dist x y
· 使用定理 `_private.Mathlib.Analysis.Normed.Group.Quotient.0.QuotientGroup.norm_aux
`：∀ {M : Type u_1} [inst : SeminormedCommGroup M] {S : Subgroup M} (x : M ⧸ S), 
{m | ↑m = x}.Nonempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `dist_one`：dist_one : dist (1 : E) = norm
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_norm_iff : r ≤ ‖x‖ ↔ ∀ m : M, ↑m = x → r ≤ ‖m‖ := by
  simp [norm_eq_infDist, le_infDist (norm_aux _)]

@[to_additive]
/-
**QuotientGroup.norm_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：norm_lt_iff : ‖x‖ < r ↔ exists m : M, ↑m = x ∧ ‖m‖ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infDist_lt_iff`：infDist_lt_iff {r : Real} (hs : s.Nonempty) : inf
Dist x s < r ↔ exists y in s, dist x y < r
· 使用定理 `_private.Mathlib.Analysis.Normed.Group.Quotient.0.QuotientGroup.norm_aux
`：∀ {M : Type u_1} [inst : SeminormedCommGroup M] {S : Subgroup M} (x : M ⧸ S), 
{m | ↑m = x}.Nonempty
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `dist_one`：dist_one : dist (1 : E) = norm
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma norm_lt_iff : ‖x‖ < r ↔ ∃ m : M, ↑m = x ∧ ‖m‖ < r := by
  simp [norm_eq_infDist, infDist_lt_iff (norm_aux _)]

@[to_additive]
/-
**QuotientGroup.nhds_one_hasBasis** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：nhds_one_hasBasis : (𝓝 (1 : M ⧸ S)).HasBasis (fun ε => 0 < ε) fun ε => {x 
| ‖x‖ < ε}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.forall_mk`：forall_mk {C : α ⧸ s -> Prop} : (forall x : α ⧸
 s, C x) ↔ forall x : α, C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_one_eq`：ball_one_eq (r : Real) : ball (1 : E) r = { x | ‖x‖ < r }
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用引理 `QuotientGroup.norm_lt_iff`：norm_lt_iff : ‖x‖ < r ↔ exists m : M, ↑m = x 
∧ ‖m‖ < r
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.mk_one`：mk_one : ((1 : G) : Q) = 1
· 使用定理 `QuotientGroup.nhds_eq`：nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) 
(𝓝 x)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `SeminormedCommGroup.toIsTopologicalGroup`：∀ {E : Type u_2} [inst : Semin
ormedCommGroup E], IsTopologicalGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
lemma nhds_one_hasBasis : (𝓝 (1 : M ⧸ S)).HasBasis (fun ε ↦ 0 < ε) fun ε ↦ {x | ‖x‖ < ε} := by
  have : ∀ ε : ℝ, mk '' ball (1 : M) ε = {x : M ⧸ S | ‖x‖ < ε} := by
    refine fun ε ↦ Set.ext <| forall_mk.2 fun x ↦ ?_
    rw [ball_one_eq, mem_ofPred_eq, norm_lt_iff, mem_image]
    exact exists_congr fun _ ↦ and_comm
  rw [← mk_one, nhds_eq, ← funext this]
  exact .map _ Metric.nhds_basis_ball

/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/
@[to_additive
/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/]
/-
**QuotientGroup.norm_mk** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：norm_mk (x : M) : ‖(x : M ⧸ S)‖ = infDist x S
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuotientGroup.norm_eq_infDist`：norm_eq_infDist (x : M ⧸ S) : ‖x‖ = infDi
st 1 {m : M | (m : M ⧸ S) = x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.infDist_image`：infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ
 '' t) = infDist x t
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.preimage_symm`：preimage_symm (h : α ≃ᵢ β) : preimage h.sym
m = image h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsometryEquiv.divLeft_apply`：∀ {G : Type v} [inst : Group G] [inst_1 : P
seudoEMetricSpace G] [inst_2 : IsIsometricSMul G G]   [inst_3 : IsIsometricSMul 
Gᵐᵒᵖ G] (c b : G)…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用定理 `IsometryEquiv.divLeft_symm_apply`：∀ {G : Type v} [inst : Group G] [inst_
1 : PseudoEMetricSpace G] [inst_2 : IsIsometricSMul G G]   [inst_3 : IsIsometric
SMul Gᵐᵒᵖ G] (c b : G)…
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_mk (x : M) : ‖(x : M ⧸ S)‖ = infDist x S := by
  rw [norm_eq_infDist, ← infDist_image (IsometryEquiv.divLeft x).isometry,
    ← IsometryEquiv.preimage_symm]
  simp

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
@[to_additive
/-- The norm of the projection is smaller or equal to the norm of the original element. -/]
/-
**QuotientGroup.norm_mk_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：norm_mk_le_norm : ‖(m : M ⧸ S)‖ <= ‖m‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `dist_one_left`：dist_one_left (a : E) : dist 1 a = ‖a‖
-/
lemma norm_mk_le_norm : ‖(m : M ⧸ S)‖ ≤ ‖m‖ :=
  (infDist_le_dist_of_mem (by simp)).trans_eq (dist_one_left _)

/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
@[to_additive /-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m`
belongs to the closure of `S`. -/]
/-
**QuotientGroup.norm_mk_eq_zero_iff_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Quoti
entGroup`。
形式化陈述：norm_mk_eq_zero_iff_mem_closure : ‖(m : M ⧸ S)‖ = 0 ↔ m in closure (S : Se
t M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuotientGroup.norm_mk`：norm_mk (x : M) : ‖(x : M ⧸ S)‖ = infDist x S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.mem_closure_iff_infDist_zero`：mem_closure_iff_infDist_zero (h : s
.Nonempty) : x in closure s ↔ infDist x s = 0
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_mk_eq_zero_iff_mem_closure : ‖(m : M ⧸ S)‖ = 0 ↔ m ∈ closure (S : Set M) := by
  rw [norm_mk, ← mem_closure_iff_infDist_zero]
  exact ⟨1, S.one_mem⟩

/-- The norm of the image of `m : M` in the quotient by a closed subgroup `S` is zero if and only if
`m ∈ S`. -/
@[to_additive /-- The norm of the image of `m : M` in the quotient by a closed subgroup `S` is zero
if and only if `m ∈ S`. -/]
/-
**QuotientGroup.norm_mk_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：norm_mk_eq_zero [hS : IsClosed (S : Set M)] : ‖(m : M ⧸ S)‖ = 0 ↔ m in S
参数：S : Set M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuotientGroup.norm_mk_eq_zero_iff_mem_closure`：norm_mk_eq_zero_iff_mem_c
losure : ‖(m : M ⧸ S)‖ = 0 ↔ m in closure (S : Set M)
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_mk_eq_zero [hS : IsClosed (S : Set M)] : ‖(m : M ⧸ S)‖ = 0 ↔ m ∈ S := by
  rw [norm_mk_eq_zero_iff_mem_closure, hS.closure_eq, SetLike.mem_coe]

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/
@[to_additive /-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/]
/-
**QuotientGroup.exists_norm_mk_lt** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：exists_norm_mk_lt (x : M ⧸ S) (hε : 0 < ε) : exists m : M, m = x ∧ ‖m‖ < ‖
x‖ + ε
参数：x : M ⧸ S；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `QuotientGroup.norm_lt_iff`：norm_lt_iff : ‖x‖ < r ↔ exists m : M, ↑m = x 
∧ ‖m‖ < r
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma exists_norm_mk_lt (x : M ⧸ S) (hε : 0 < ε) : ∃ m : M, m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_lt_iff.1 <| lt_add_of_pos_right _ hε

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m * s‖ < ‖mk' S m‖ + ε`. -/
@[to_additive
/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m + s‖ < ‖mk' S m‖ + ε`. -/]
/-
**QuotientGroup.exists_norm_mul_lt** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：exists_norm_mul_lt (S : Subgroup M) (m : M) {ε : Real} (hε : 0 < ε) : exis
ts s in S, ‖m * s‖ < ‖mk' S m‖ + ε
参数：S : Subgroup M；m : M；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_isMulCommutative`：∀ {G : Type u_1} [inst : Group G] [
IsMulCommutative G] (H : Subgroup G), H.Normal
· 使用引理 `QuotientGroup.exists_norm_mk_lt`：exists_norm_mk_lt (x : M ⧸ S) (hε : 0 <
 ε) : exists m : M, m = x ∧ ‖m‖ < ‖x‖ + ε
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
lemma exists_norm_mul_lt (S : Subgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖m * s‖ < ‖mk' S m‖ + ε := by
  obtain ⟨n : M, hn, hn'⟩ := exists_norm_mk_lt (QuotientGroup.mk' S m) hε
  exact ⟨m⁻¹ * n, by simpa [eq_comm, QuotientGroup.eq] using hn, by simpa⟩

variable (S) in
/-- The seminormed group structure on the quotient by a subgroup. -/
@[to_additive /-- The seminormed group structure on the quotient by an additive subgroup. -/]
/-
**QuotientGroup.instSeminormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup
`。
形式化陈述：instSeminormedCommGroup : SeminormedCommGroup (M ⧸ S) where toUniformSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The seminormed group structure on the quotient by a subgroup.
-/
noncomputable instance instSeminormedCommGroup : SeminormedCommGroup (M ⧸ S) where
  toUniformSpace := IsTopologicalGroup.leftUniformSpace (M ⧸ S)
  __ := groupSeminorm.toSeminormedCommGroup
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_one_left, (nhds_one_hasBasis.comap _).eq_biInf]
    simp only [dist, preimage_ofPred_eq, norm_eq_groupSeminorm]

variable (S) in
/-- The quotient in the category of normed groups. -/
@[to_additive /-- The quotient in the category of normed groups. -/]
/-
**QuotientGroup.instNormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
形式化陈述：instNormedCommGroup [hS : IsClosed (S : Set M)] : NormedCommGroup (M ⧸ S) 
where __
参数：S : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient in the category of normed groups.
-/
noncomputable instance instNormedCommGroup [hS : IsClosed (S : Set M)] :
    NormedCommGroup (M ⧸ S) where
  __ := MetricSpace.ofT0PseudoMetricSpace _

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
/-
**QuotientGroup.** 是 Mathlib 中的一个示例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example :
    (instTopologicalSpaceQuotient : TopologicalSpace <| M ⧸ S) =
      (instSeminormedCommGroup S).toUniformSpace.toTopologicalSpace := rfl
/-
**QuotientGroup.** 是 Mathlib 中的一个示例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [IsClosed (S : Set M)] :
    (instSeminormedCommGroup S) = NormedCommGroup.toSeminormedCommGroup := rfl

/-- An isometric version of `Subgroup.quotientEquivOfEq`. -/
@[to_additive /-- An isometric version of `AddSubgroup.quotientEquivOfEq`. -/]
/-
**QuotientGroup._root_.Subgroup.quotientIsometryEquivOfEq** 是 Mathlib 中的一个定义，位于命
名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric version of `Subgroup.quotientEquivOfEq`.
-/
def _root_.Subgroup.quotientIsometryEquivOfEq (h : S = T) : M ⧸ S ≃ᵢ M ⧸ T where
  __ := Subgroup.quotientEquivOfEq h
  isometry_toFun := by subst h; rintro ⟨_⟩ ⟨_⟩; rfl

/-- An isometric version of `QuotientGroup.quotientBot`. -/
@[to_additive /-- An isometric version of `QuotientAddGroup.quotientBot`. -/]
/-
**QuotientGroup.quotientBotIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGrou
p`。
形式化陈述：quotientBotIsometryEquiv : M ⧸ (⊥ : Subgroup M) ≃ᵢ M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric version of `QuotientGroup.quotientBot`.
-/
def quotientBotIsometryEquiv : M ⧸ (⊥ : Subgroup M) ≃ᵢ M where
  __ := quotientBot
  isometry_toFun : Isometry quotientBot := by
    rw [MonoidHomClass.isometry_iff_norm]
    rintro ⟨x⟩
    change ‖x‖ = ‖QuotientGroup.mk x‖
    simp [norm_mk]

/-- An isometric version of `QuotientGroup.quotientQuotientEquivQuotient`. -/
@[to_additive /-- An isometric version of `QuotientAddGroup.quotientQuotientEquivQuotient`. -/]
/-
**QuotientGroup.quotientQuotientIsometryEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 
`QuotientGroup`。
形式化陈述：quotientQuotientIsometryEquivQuotient (h : S <= T) : (M ⧸ S) ⧸ T.map (mk' 
S) ≃ᵢ M ⧸ T where __
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric version of `QuotientGroup.quotientQuotientEquivQuotient`.
-/
def quotientQuotientIsometryEquivQuotient (h : S ≤ T) : (M ⧸ S) ⧸ T.map (mk' S) ≃ᵢ M ⧸ T where
  __ := quotientQuotientEquivQuotient S T h
  isometry_toFun : Isometry (quotientQuotientEquivQuotient S T h) := by
    rw [MonoidHomClass.isometry_iff_norm]
    refine fun x => eq_of_forall_le_iff fun r => ?_
    simp only [le_norm_iff]
    exact ⟨
      fun h₁ y h₂ z h₃ => h₁ z <| by subst_vars; rfl,
      fun h₁ y h₂ => h₁ y ((quotientQuotientEquivQuotient S T h).injective h₂) y rfl⟩

end QuotientGroup

open QuotientAddGroup Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/-- The norm of the image under the natural morphism to the quotient. -/
/-
**quotient_norm_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quotient_norm_mk_eq (S : AddSubgroup M) (m : M) : ‖mk' S m‖ = sInf ((‖m + 
·‖) '' S)
参数：S : AddSubgroup M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientAddGroup.mk'_apply`：∀ {G : Type u_1} [inst : AddGroup G] (N : Ad
dSubgroup G) [nN : N.Normal] (x : G), (QuotientAddGroup.mk' N) x = ↑x
· 使用定理 `QuotientAddGroup.norm_mk`：∀ {M : Type u_1} [inst : SeminormedAddCommGrou
p M] {S : AddSubgroup M} (x : M), ‖↑x‖ = Metric.infDist x ↑S
· 使用定理 `sInf_image'`：∀ {α : Type u_1} {β : Type u_2} [inst : InfSet α] {s : Set 
β} {f : β → α}, sInf (f '' s) = ⨅ a, f ↑a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.infDist_image`：infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ
 '' t) = infDist x t
· 使用定理 `isometry_neg`：∀ {G : Type v} [inst : AddGroup G] [inst_1 : PseudoEMetric
Space G] [IsIsometricVAdd G G] [IsIsometricVAdd Gᵃᵒᵖ G],   Isometry Neg.neg
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `NormedAddGroup.to_isIsometricVAdd_right`：∀ {E : Type u_2} [inst : Semino
rmedAddCommGroup E], IsIsometricVAdd Eᵃᵒᵖ E
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
· 使用定理 `neg_coe_set`：∀ {G : Type u_2} {S : Type u_4} [inst : InvolutiveNeg G] [i
nst_1 : SetLike S G] [NegMemClass S G] {H : S}, -↑H = ↑H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `Metric.infDist_eq_iInf`：infDist_eq_iInf : infDist x s = ⨅ y : s, dist x 
y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm of the image under the natural morphism to the quotient.
-/
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = sInf ((‖m + ·‖) '' S) := by
  rw [mk'_apply, norm_mk, sInf_image', ← infDist_image isometry_neg, image_neg_eq_neg,
    neg_coe_set (H := S), infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]

/-- The quotient norm satisfies the triangle inequality. -/
/-
**quotient_norm_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ <= ‖x‖ + 
‖y‖
参数：S : AddSubgroup M；x y : M ⧸ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖

--- 原说明 ---
The quotient norm satisfies the triangle inequality.
-/
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

namespace AddSubgroup

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by a subgroup. -/
/-
**AddSubgroup.normedMk** 是 Mathlib 中的一个定义，位于命名空间 `AddSubgroup`。
形式化陈述：normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) where __
参数：S : AddSubgroup M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from a seminormed group to the quotient by a subgroup.
-/
noncomputable def normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) where
  __ := QuotientAddGroup.mk' S
  bound' := ⟨1, fun m => by simpa [one_mul] using norm_mk_le_norm⟩

/-- `S.normedMk` agrees with `QuotientAddGroup.mk' S`. -/
@[simp]
/-
**AddSubgroup.normedMk.apply** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup.normedMk`。
形式化陈述：∀ {M : Type u_1} [inst : SeminormedAddCommGroup M] (S : AddSubgroup M) (m 
: M),   S.normedMk m = (QuotientAddGroup.mk' S) m
参数：S : AddSubgroup M；m : M；QuotientAddGroup.mk' S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S.normedMk` agrees with `QuotientAddGroup.mk' S`.
-/
theorem normedMk.apply (S : AddSubgroup M) (m : M) : normedMk S m = QuotientAddGroup.mk' S m :=
  rfl

/-- `S.normedMk` is surjective. -/
/-
**AddSubgroup.surjective_normedMk** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S)
参数：S : AddSubgroup M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)

--- 原说明 ---
`S.normedMk` is surjective.
-/
theorem surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S) :=
  Quot.mk_surjective

/-- The kernel of `S.normedMk` is `S`. -/
/-
**AddSubgroup.ker_normedMk** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S
参数：S : AddSubgroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.ker_mk'`：∀ {G : Type u_1} [inst : AddGroup G] (N : AddS
ubgroup G) [nN : N.Normal], (QuotientAddGroup.mk' N).ker = N

--- 原说明 ---
The kernel of `S.normedMk` is `S`.
-/
theorem ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S :=
  QuotientAddGroup.ker_mk' _

/-- The operator norm of the projection is at most `1`. -/
/-
**AddSubgroup.norm_normedMk_le** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ <= 1
参数：S : AddSubgroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The operator norm of the projection is at most `1`.
-/
theorem norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [norm_mk_le_norm]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddSubgroup._root_.QuotientAddGroup.norm_lift_apply_le** 是 Mathlib 中的一个定理，位于命名
空间 `AddSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.QuotientAddGroup.norm_lift_apply_le {S : AddSubgroup M} (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ S, f x = 0) (x : M ⧸ S) : ‖lift S f.toAddMonoidHom hf x‖ ≤ ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_lt' with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt, ← lt_div_iff₀' h, norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff₀' h).1 hx).not_ge (le_opNorm f x)

/-- The operator norm of the projection is `1` if the subspace is not dense. -/
/-
**AddSubgroup.norm_normedMk** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) != u
niv) : ‖S.normedMk‖ = 1
参数：S : AddSubgroup M；h : (S.topologicalClosure : Set M) != univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddSubgroup.norm_normedMk_le`：norm_normedMk_le (S : AddSubgroup M) : ‖S.
normedMk‖ <= 1
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure`：∀ {M : Type u_1} [inst
 : SeminormedAddCommGroup M] {S : AddSubgroup M} {m : M}, ‖↑m‖ = 0 ↔ m ∈ closure
 ↑S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用引理 `le_mul_iff_one_le_left`：le_mul_iff_one_le_left [MulPosMono α] [MulPosRef
lectLE α] (a0 : 0 < a) : a <= b * a ↔ 1 <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `QuotientAddGroup.norm_lift_apply_le`：∀ {M : Type u_1} {N : Type u_2} [in
st : SeminormedAddCommGroup M] [inst_1 : SeminormedAddCommGroup N]   {S : AddSub
group M} (f : NormedAddGr…
· 使用定理 `QuotientAddGroup.eq_zero_iff`：∀ {G : Type u_1} [inst : AddGroup G] {N : 
AddSubgroup G} [inst_1 : N.Normal] (x : G), ↑x = 0 ↔ x ∈ N

--- 原说明 ---
The operator norm of the projection is `1` if the subspace is not dense.
-/
theorem norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) ≠ univ) :
    ‖S.normedMk‖ = 1 := by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : ∃ x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx ↦ ?_
    exact (norm_nonneg _).lt_of_ne' <| mt norm_mk_eq_zero_iff_mem_closure.1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le S.normedMk (fun x ↦ (eq_zero_iff x).2) x

/-- The operator norm of the projection is `0` if the subspace is dense. -/
/-
**AddSubgroup.norm_trivial_quotient_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup`。
形式化陈述：norm_trivial_quotient_mk (S : AddSubgroup M) (h : (S.topologicalClosure : 
Set M) = Set.univ) : ‖S.normedMk‖ = 0
参数：S : AddSubgroup M；h : (S.topologicalClosure : Set M) = Set.univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.ker_normedMk`：ker_normedMk (S : AddSubgroup M) : S.normedMk.
ker = S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure`：∀ {M : Type u_1} [inst
 : SeminormedAddCommGroup M] {S : AddSubgroup M} {m : M}, ‖↑m‖ = 0 ↔ m ∈ closure
 ↑S
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
The operator norm of the projection is `0` if the subspace is dense.
-/
theorem norm_trivial_quotient_mk (S : AddSubgroup M)
    (h : (S.topologicalClosure : Set M) = Set.univ) : ‖S.normedMk‖ = 0 := by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
  have hker : x ∈ S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk, ← SetLike.mem_coe, h]
    trivial
  rw [ker_normedMk] at hker
  simp [norm_mk_eq_zero_iff_mem_closure.mpr hker]

end AddSubgroup

namespace NormedAddGroupHom

/-- `IsQuotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
/-
**NormedAddGroupHom.IsQuotient** 是 Mathlib 中的一个归纳类型，位于命名空间 `NormedAddGroupHom`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     [inst : SeminormedAddCommGroup M] 
→ [inst_1 : SeminormedAddCommGroup N] → NormedAddGroupHom M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsQuotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of 
`M`
by the kernel of `f`.
-/
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : ∀ x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)

/-- Given `f : NormedAddGroupHom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : AddSubgroup M` is closed, the induced morphism `NormedAddGroupHom (M ⧸ S) N`. -/
/-
**NormedAddGroupHom.lift** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M) (f : Norme
dAddGroupHom M N) (hf : forall s in S, f s = 0) : NormedAddGroupHom (M ⧸ S) N
参数：S : AddSubgroup M；f : NormedAddGroupHom M N；hf : forall s in S, f s = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : NormedAddGroupHom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : AddSubgroup M` is closed, the induced morphism `NormedAddGroupHom (M ⧸ S) N
`.
-/
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }
/-
**NormedAddGroupHom.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：lift_mk {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M) (f : No
rmedAddGroupHom M N) (hf : forall s in S, f s = 0) (m : M) : lift S f hf (S.norm
edMk m) = f m
参数：S : AddSubgroup M；f : NormedAddGroupHom M N；hf : forall s in S, f s = 0；m : M
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
    lift S f hf (S.normedMk m) = f m :=
  rfl
/-
**NormedAddGroupHom.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：lift_unique {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M) (f 
: NormedAddGroupHom M N) (hf : forall s in S, f s = 0) (g : NormedAddGroupHom (M
 ⧸ S) N) (h : g.comp S.normedMk = f) : g = lift S f hf
参数：S : AddSubgroup M；f : NormedAddGroupHom M N；hf : forall s in S, f s = 0；g : N
ormedAddGroupHom (M ⧸ S) N；h : g.comp S.normedMk = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `AddSubgroup.surjective_normedMk`：surjective_normedMk (S : AddSubgroup M)
 : Function.Surjective (normedMk S)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (g : NormedAddGroupHom (M ⧸ S) N)
    (h : g.comp S.normedMk = f) : g = lift S f hf := by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl

/-- `S.normedMk` satisfies `IsQuotient`. -/
/-
**NormedAddGroupHom.isQuotientQuotient** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroup
Hom`。
形式化陈述：isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk
参数：S : AddSubgroup M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.surjective_normedMk`：surjective_normedMk (S : AddSubgroup M)
 : Function.Surjective (normedMk S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.ker_normedMk`：ker_normedMk (S : AddSubgroup M) : S.normedMk.
ker = S
· 使用定理 `quotient_norm_mk_eq`：quotient_norm_mk_eq (S : AddSubgroup M) (m : M) : ‖
mk' S m‖ = sInf ((‖m + ·‖) '' S)

--- 原说明 ---
`S.normedMk` satisfies `IsQuotient`.
-/
theorem isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk :=
  ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩
/-
**NormedAddGroupHom.IsQuotient.norm_lift** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGro
upHom.IsQuotient`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : SeminormedAddCommGroup M] [inst_1 
: SeminormedAddCommGroup N]   {f : NormedAddGroupHom M N}, f.IsQuotient → ∀ {ε :
 ℝ}, 0 < ε → ∀ (n : N), ∃ m, f m = n ∧ ‖m‖ < ‖n‖ + ε
参数：n : N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.IsQuotient.surjective`：∀ {M : Type u_1} {N : Type u_2}
 [inst : SeminormedAddCommGroup M] [inst_1 : SeminormedAddCommGroup N]   {f : No
rmedAddGroupHom M N}, f.IsQuo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `AddSubgroup.zero_mem`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSubgr
oup G), 0 ∈ H
· 使用定理 `Real.lt_sInf_add_pos`：lt_sInf_add_pos (h : s.Nonempty) {ε : Real} (hε : 
0 < ε) : exists a in s, a < sInf s + ε
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedAddGroupHom.mem_ker`：mem_ker (v : V₁) : v in f.ker ↔ f v = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `NormedAddGroupHom.IsQuotient.norm`：∀ {M : Type u_1} {N : Type u_2} [inst
 : SeminormedAddCommGroup M] [inst_1 : SeminormedAddCommGroup N]   {f : NormedAd
dGroupHom M N}, f.IsQuo…
-/
theorem IsQuotient.norm_lift {f : NormedAddGroupHom M N} (hquot : IsQuotient f) {ε : ℝ} (hε : 0 < ε)
    (n : N) : ∃ m : M, f m = n ∧ ‖m‖ < ‖n‖ + ε := by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty := by
    rw [Set.image_nonempty]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_sInf_add_pos nonemp hε
    with ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < sInf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact ⟨m + x, by rw [map_add, (NormedAddGroupHom.mem_ker f x).mp hx, add_zero], by
    rwa [hquot.norm]⟩
/-
**NormedAddGroupHom.IsQuotient.norm_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroup
Hom.IsQuotient`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : SeminormedAddCommGroup M] [inst_1 
: SeminormedAddCommGroup N]   {f : NormedAddGroupHom M N}, f.IsQuotient → ∀ (m :
 M), ‖f m‖ ≤ ‖m‖
参数：m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.IsQuotient.norm`：∀ {M : Type u_1} {N : Type u_2} [inst
 : SeminormedAddCommGroup M] [inst_1 : SeminormedAddCommGroup N]   {f : NormedAd
dGroupHom M N}, f.IsQuo…
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `AddSubgroup.zero_mem`：∀ {G : Type u_1} [inst : AddGroup G] (H : AddSubgr
oup G), 0 ∈ H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
    ‖f m‖ ≤ ‖m‖ := by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩
/-
**NormedAddGroupHom.norm_lift_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M) (f
 : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) : ‖lift S f hf‖ <= ‖f‖
参数：S : AddSubgroup M；f : NormedAddGroupHom M N；hf : forall s in S, f s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `QuotientAddGroup.norm_lift_apply_le`：∀ {M : Type u_1} {N : Type u_2} [in
st : SeminormedAddCommGroup M] [inst_1 : SeminormedAddCommGroup N]   {S : AddSub
group M} (f : NormedAddGr…
-/
theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) :
    ‖lift S f hf‖ ≤ ‖f‖ :=
  opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

-- TODO: deprecate?
/-
**NormedAddGroupHom.lift_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：lift_norm_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M) (f
 : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) {c : Real>=0} (fb : ‖f‖ 
<= c) : ‖lift S f hf‖ <= c
参数：S : AddSubgroup M；f : NormedAddGroupHom M N；hf : forall s in S, f s = 0；fb : 
‖f‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NormedAddGroupHom.norm_lift_le`：norm_lift_le {N : Type*} [SeminormedAddC
ommGroup N] (S : AddSubgroup M) (f : NormedAddGroupHom M N) (hf : forall s in S,
 f s = 0) : ‖lift S …
-/
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖lift S f hf‖ ≤ c :=
  (norm_lift_le S f hf).trans fb
/-
**NormedAddGroupHom.lift_normNoninc** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
 (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) (fb : f.NormNoninc) :
 (lift S f hf).NormNoninc
参数：S : AddSubgroup M；f : NormedAddGroupHom M N；hf : forall s in S, f s = 0；fb : 
f.NormNoninc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one`：normNoninc_iff_
norm_le_one : f.NormNoninc ↔ ‖f‖ <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NormedAddGroupHom.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖ <
= c) (x : V₁) : ‖f x‖ <= c * ‖x‖
· 使用定理 `NormedAddGroupHom.lift_norm_le`：lift_norm_le {N : Type*} [SeminormedAddC
ommGroup N] (S : AddSubgroup M) (f : NormedAddGroupHom M N) (hf : forall s in S,
 f s = 0) {c : Real>…
-/
theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (fb : f.NormNoninc) :
    (lift S f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _

end NormedAddGroupHom

/-!
### Submodules and ideals

In what follows, the norm structures created above for quotients of (semi)`NormedAddCommGroup`s
by `AddSubgroup`s are transferred via definitional equality to quotients of modules by submodules,
and of rings by ideals, thereby preserving the definitional equality for the topological group and
uniform structures worked for above. Completeness is also transferred via this definitional
equality.

In addition, instances are constructed for `NormedSpace`, `SeminormedCommRing`,
`NormedCommRing` and `NormedAlgebra` under the appropriate hypotheses. Currently, we do not
have quotients of rings by two-sided ideals, hence the commutativity hypotheses are required.
-/

section Submodule

variable {R : Type*} [Ring R] [Module R M] (S T : Submodule R M)

/-
**Submodule.Quotient.seminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.Quotient.seminormedAddCommGroup : SeminormedAddCommGroup (M ⧸ S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Submodule.Quotient.seminormedAddCommGroup : SeminormedAddCommGroup (M ⧸ S) :=
  inferInstanceAs <| SeminormedAddCommGroup (M ⧸ S.toAddSubgroup)
/-
**Submodule.Quotient.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.Quotient.normedAddCommGroup [hS : IsClosed (S : Set M)] : Normed
AddCommGroup (M ⧸ S)
参数：S : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Submodule.Quotient.normedAddCommGroup [hS : IsClosed (S : Set M)] :
    NormedAddCommGroup (M ⧸ S) :=
  inferInstanceAs <| NormedAddCommGroup (M ⧸ S.toAddSubgroup)
/-
**Submodule.Quotient.completeSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.Quotient.completeSpace [CompleteSpace M] : CompleteSpace (M ⧸ S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.completeSpace_left`：∀ (G : Type u_1) [inst : AddGroup G
] [us : UniformSpace G] [inst_1 : IsLeftUniformAddGroup G] [FirstCountableTopolo
gy G]   (N : AddSubgroup …
· 使用定理 `IsUniformAddGroup.isLeftUniformAddGroup`：∀ (α : Type u_1) [inst : Unifor
mSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsLeftUniformAddGroup α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
-/
instance Submodule.Quotient.completeSpace [CompleteSpace M] : CompleteSpace (M ⧸ S) :=
  QuotientAddGroup.completeSpace_left M S.toAddSubgroup

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `Submodule.Quotient.mk m = x`
and `‖m‖ < ‖x‖ + ε`. -/
nonrec theorem Submodule.Quotient.norm_mk_lt {S : Submodule R M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  exists_norm_mk_lt x hε

/-
**Submodule.Quotient.norm_mk_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)
‖ <= ‖m‖
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.norm_mk_le_norm`：∀ {M : Type u_1} [inst : SeminormedAdd
CommGroup M] {S : AddSubgroup M} {m : M}, ‖↑m‖ ≤ ‖m‖
-/
theorem Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ≤ ‖m‖ :=
  norm_mk_le_norm
/-
**Submodule.Quotient.instIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.Quotient.instIsBoundedSMul (𝕜 : Type*) [SeminormedCommRing 𝕜] [M
odule 𝕜 M] [IsBoundedSMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] : IsBoundedSMul 
𝕜 (M ⧸ S)
参数：𝕜 : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_norm_smul_le`：IsBoundedSMul.of_norm_smul_le (h : forall
 (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖) : IsBoundedSMul α β
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Real.uniformContinuous_const_mul`：Real.uniformContinuous_const_mul {x : 
Real} : UniformContinuous (x * ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.Quotient.norm_mk_lt`：∀ {M : Type u_1} [inst : SeminormedAddCom
mGroup M] {R : Type u_3} [inst_1 : Ring R] [inst_2 : _root_.Module R M]   {S : S
ubmodule R M} (x : …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.Quotient.norm_mk_le`：Submodule.Quotient.norm_mk_le (m : M) : ‖
(Submodule.Quotient.mk m : M ⧸ S)‖ <= ‖m‖
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
（共 60 条，此处仅展示前 30 条）
-/
instance Submodule.Quotient.instIsBoundedSMul (𝕜 : Type*)
    [SeminormedCommRing 𝕜] [Module 𝕜 M] [IsBoundedSMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] :
    IsBoundedSMul 𝕜 (M ⧸ S) :=
  .of_norm_smul_le fun k x =>
    -- this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M ⧸ S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
        ((@Real.uniformContinuous_const_mul ‖k‖).continuous.tendsto ‖x‖) ε hε
      simp only [mem_ball, dist, abs_sub_lt_iff] at this
      rcases this with ⟨δ, hδ, h⟩
      obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ
      specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le S a]⟩
      calc
        _ ≤ ‖k‖ * ‖a‖ := (norm_mk_le ..).trans (norm_smul_le k a)
        _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
/-
**Submodule.Quotient.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.Quotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 
M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) where norm_smul_le
参数：𝕜 : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Submodule.Quotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
    [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) where
  norm_smul_le := norm_smul_le

/-- An isometric version of `Submodule.quotEquivOfEq`. -/
/-
**Submodule.quotLIEOfEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.quotLIEOfEq (h : S = T) : M ⧸ S ≃ₗᵢ[R] M ⧸ T where __
参数：h : S = T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric version of `Submodule.quotEquivOfEq`.
-/
def Submodule.quotLIEOfEq (h : S = T) : M ⧸ S ≃ₗᵢ[R] M ⧸ T where
  __ := Submodule.quotEquivOfEq S T h
  norm_map' := by subst h; rintro ⟨_⟩; rfl

/-- An isometric version of `Submodule.quotientQuotientEquivQuotient`. -/
/-
**Submodule.quotientQuotientLIEQuotient** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.quotientQuotientLIEQuotient (h : S <= T) : (M ⧸ S) ⧸ map S.mkQ T
 ≃ₗᵢ[R] M ⧸ T where __
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric version of `Submodule.quotientQuotientEquivQuotient`.
-/
def Submodule.quotientQuotientLIEQuotient (h : S ≤ T) : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M ⧸ T where
  __ := Submodule.quotientQuotientEquivQuotient S T h
  norm_map' :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (QuotientAddGroup.quotientQuotientIsometryEquivQuotient
        ((Submodule.toAddSubgroup_le S T).mpr h)).isometry

/-- An isometric version of `Submodule.quotientQuotientEquivQuotientSup`. -/
/-
**Submodule.quotientQuotientLIEQuotientSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.quotientQuotientLIEQuotientSup : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M 
⧸ (S ⊔ T)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric version of `Submodule.quotientQuotientEquivQuotientSup`.
-/
def Submodule.quotientQuotientLIEQuotientSup : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M ⧸ (S ⊔ T) :=
  (quotLIEOfEq _ _ (by simp)).trans (quotientQuotientLIEQuotient _ _ le_sup_left)

end Submodule

section Ideal

variable {R : Type*} [SeminormedCommRing R] (I : Ideal R)

nonrec theorem Ideal.Quotient.norm_mk_lt {I : Ideal R} (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  exists_norm_mk_lt x hε

/-
**Ideal.Quotient.norm_mk_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ <= ‖r‖
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.norm_mk_le_norm`：∀ {M : Type u_1} [inst : SeminormedAdd
CommGroup M] {S : AddSubgroup M} {m : M}, ‖↑m‖ ≤ ‖m‖
-/
theorem Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ ≤ ‖r‖ := norm_mk_le_norm
/-
**Ideal.Quotient.semiNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) where dist_
eq
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  mul_comm := _root_.mul_comm
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := Ideal.Quotient.norm_mk_lt x h₁,
      Ideal.Quotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I a]⟩
      ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (Ideal.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
/-
**Ideal.Quotient.normedCommRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸
 I)
参数：I : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) :=
  { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }

variable (𝕜 : Type*) [NormedField 𝕜]
/-
**Ideal.Quotient.normedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

end Ideal

