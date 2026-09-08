/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Erdős-Kaplansky theorem

* `rank_dual_eq_card_dual_of_aleph0_le_rank`: The **Erdős-Kaplansky Theorem** which says that
  the dimension of an infinite-dimensional dual space over a division ring has dimension
  equal to its cardinality.

-/

public section

noncomputable section

universe u v

variable {K : Type u}

open Cardinal

section Cardinal

variable (K)
variable [DivisionRing K]

/-- Key lemma towards the Erdős-Kaplansky theorem from https://mathoverflow.net/a/168624 -/
/-
**max_aleph0_card_le_rank_fun_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_aleph0_card_le_rank_fun_nat : max ℵ₀ #K <= Module.rank K (Nat -> K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_finsupp_self`：rank_finsupp_self (ι : Type w) : Module.rank R (ι ->₀
 R) = Cardinal.lift.{u} #ι
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Subfield.cardinalMk_closure_le_max`：cardinalMk_closure_le_max : #(closur
e s) <= max #s ℵ₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.aleph0.eq_1`：Cardinal.aleph0 = Cardinal.lift.{u, 0} (Cardinal.m
k ℕ)
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.mul_aleph0_eq`：mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ <= a) : a 
* ℵ₀ = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
Key lemma towards the Erdős-Kaplansky theorem from https://mathoverflow.net/a/16
8624
-/
theorem max_aleph0_card_le_rank_fun_nat : max ℵ₀ #K ≤ Module.rank K (ℕ → K) := by
  have aleph0_le : ℵ₀ ≤ Module.rank K (ℕ → K) := (rank_finsupp_self K ℕ).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact DFunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_gt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ℕ → K)
  let L := Subfield.closure (Set.range (fun i : ιK × ℕ ↦ bK i.1 i.2))
  have hLK : #L < #K := by
    refine (Subfield.cardinalMk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, bK.mk_eq_rank'', mul_aleph0_eq aleph0_le]
  let := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ ≤ #ιL := by
    contrapose! hLK
    have := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq, mk_finsupp_of_fintype,
        ← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K natCast_lt_aleph0).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.linearCombination_repr (bL ∘ e)
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  let f i (j : s) : L := ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h ↦ by
    have := h.cardinal_lift_le_rank
    rw [lift_uzero, (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq,
        rank_fun'] at this
    exact natCast_lt_aleph0.not_ge this
  obtain ⟨t, g, eq0, i, hi, hgi⟩ := not_linearIndependent_iff.mp this
  refine hgi (linearIndependent_iff'.mp (bL.linearIndependent.comp e e.injective) t g ?_ i hi)
  clear_value c s
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply, map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ ↦ mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

variable {K}

open Function in
/-
**rank_fun_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Module.rank K (ι -> K) 
= #(ι -> K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.aleph0_le_mk_iff`：aleph0_le_mk_iff : ℵ₀ <= #α ↔ Infinite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `LinearMap.lift_rank_le_of_injective`：LinearMap.lift_rank_le_of_injective
 (f : M ->ₗ[R] M') (i : Injective f) : Cardinal.lift.{v'} (Module.rank R M) <= C
ardinal.lift.{v} (Module.…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearMap.funLeft_injective_of_surjective`：funLeft_injective_of_surjecti
ve (f : m -> n) (hf : Surjective f) : Injective (funLeft R M f)
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `max_aleph0_card_le_rank_fun_nat`：max_aleph0_card_le_rank_fun_nat : max ℵ
₀ #K <= Module.rank K (Nat -> K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
（共 34 条，此处仅展示前 30 条）
-/
theorem rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Module.rank K (ι → K) = #(ι → K) := by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι → K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
  have := LinearMap.lift_rank_le_of_injective _ <|
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u, v}, lift_id'.{u, v}] at this
  have key := (lift_le.{v}.mpr <| max_aleph0_card_le_rank_fun_nat K).trans this
  rw [lift_max, lift_aleph0, max_le_iff] at key
  have : Infinite ιK := by
    rw [← aleph0_le_mk_iff, bK.mk_eq_rank'']; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq, mk_finsupp_lift_of_infinite,
      lift_umax.{u, v}, lift_id'.{u, v}, bK.mk_eq_rank'', eq_comm, max_eq_left]
  exact key.2

/-- The **Erdős-Kaplansky Theorem**: the dual of an infinite-dimensional vector space
  over a division ring has dimension equal to its cardinality. -/
/-
**rank_dual_eq_card_dual_of_aleph0_le_rank'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_dual_eq_card_dual_of_aleph0_le_rank' {V : Type*} [AddCommGroup V] [Mo
dule K V] (h : ℵ₀ <= Module.rank K V) : Module.rank Kᵐᵒᵖ (V ->ₗ[K] K) = #(V ->ₗ[
K] K)
参数：h : ℵ₀ <= Module.rank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `rank_fun_infinite`：rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Mo
dule.rank K (ι -> K) = #(ι -> K)
· 使用引理 `Cardinal.aleph0_le_mk_iff`：aleph0_le_mk_iff : ℵ₀ <= #α ↔ Infinite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
The **Erdős-Kaplansky Theorem**: the dual of an infinite-dimensional vector spac
e
  over a division ring has dimension equal to its cardinality.
-/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank Kᵐᵒᵖ (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_fun_infinite

/-- The **Erdős-Kaplansky Theorem** over a field. -/
/-
**rank_dual_eq_card_dual_of_aleph0_le_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_dual_eq_card_dual_of_aleph0_le_rank {K V} [Field K] [AddCommGroup V] 
[Module K V] (h : ℵ₀ <= Module.rank K V) : Module.rank K (V ->ₗ[K] K) = #(V ->ₗ[
K] K)
参数：h : ℵ₀ <= Module.rank K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `rank_fun_infinite`：rank_fun_infinite {ι : Type v} [hι : Infinite ι] : Mo
dule.rank K (ι -> K) = #(ι -> K)
· 使用引理 `Cardinal.aleph0_le_mk_iff`：aleph0_le_mk_iff : ℵ₀ <= #α ↔ Infinite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R

--- 原说明 ---
The **Erdős-Kaplansky Theorem** over a field.
-/
theorem rank_dual_eq_card_dual_of_aleph0_le_rank {K V} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_fun_infinite
/-
**lift_rank_lt_rank_dual'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_lt_rank_dual' {V : Type v} [AddCommGroup V] [Module K V] (h : ℵ₀
 <= Module.rank K V) : Cardinal.lift.{u} (Module.rank K V) < Module.rank Kᵐᵒᵖ (V
 ->ₗ[K] K)
参数：h : ℵ₀ <= Module.rank K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `rank_dual_eq_card_dual_of_aleph0_le_rank'`：rank_dual_eq_card_dual_of_ale
ph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank K 
V) : Module.rank Kᵐᵒᵖ (V ->ₗ[K]…
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Cardinal.mk_arrow`：mk_arrow (α : Type u) (β : Type v) : #(α -> β) = (lif
t.{u} #β ^ lift.{v} #α)
· 使用定理 `Cardinal.cantor'`：cantor' (a) {b : Cardinal} (hb : 1 < b) : a < b ^ a
· 使用定理 `Cardinal.one_lt_lift_iff`：one_lt_lift_iff {a : Cardinal.{u}} : (1 : Card
inal) < lift.{v} a ↔ 1 < a
· 使用定理 `Cardinal.one_lt_iff_nontrivial`：one_lt_iff_nontrivial {α : Type u} : 1 <
 #α ↔ Nontrivial α
-/
theorem lift_rank_lt_rank_dual' {V : Type v} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [← b.mk_eq_rank'', rank_dual_eq_card_dual_of_aleph0_le_rank' h,
      ← (b.constr ℕ (M' := K)).toEquiv.cardinal_eq, mk_arrow]
  apply cantor'
  rw [one_lt_lift_iff, one_lt_iff_nontrivial]
  infer_instance
/-
**lift_rank_lt_rank_dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_lt_rank_dual {K : Type u} {V : Type v} [Field K] [AddCommGroup V
] [Module K V] (h : ℵ₀ <= Module.rank K V) : Cardinal.lift.{u} (Module.rank K V)
 < Module.rank K (V ->ₗ[K] K)
参数：h : ℵ₀ <= Module.rank K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_dual_eq_card_dual_of_aleph0_le_rank`：rank_dual_eq_card_dual_of_alep
h0_le_rank {K V} [Field K] [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank 
K V) : Module.rank K (V ->ₗ[K]…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_dual_eq_card_dual_of_aleph0_le_rank'`：rank_dual_eq_card_dual_of_ale
ph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank K 
V) : Module.rank Kᵐᵒᵖ (V ->ₗ[K]…
· 使用定理 `lift_rank_lt_rank_dual'`：lift_rank_lt_rank_dual' {V : Type v} [AddCommGr
oup V] [Module K V] (h : ℵ₀ <= Module.rank K V) : Cardinal.lift.{u} (Module.rank
 K V) < Modul…
-/
theorem lift_rank_lt_rank_dual {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank K (V →ₗ[K] K) := by
  rw [rank_dual_eq_card_dual_of_aleph0_le_rank h, ← rank_dual_eq_card_dual_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h
/-
**rank_lt_rank_dual'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_lt_rank_dual' {V : Type u} [AddCommGroup V] [Module K V] (h : ℵ₀ <= M
odule.rank K V) : Module.rank K V < Module.rank Kᵐᵒᵖ (V ->ₗ[K] K)
参数：h : ℵ₀ <= Module.rank K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_lt_rank_dual'`：lift_rank_lt_rank_dual' {V : Type v} [AddCommGr
oup V] [Module K V] (h : ℵ₀ <= Module.rank K V) : Cardinal.lift.{u} (Module.rank
 K V) < Modul…
-/
theorem rank_lt_rank_dual' {V : Type u} [AddCommGroup V] [Module K V] (h : ℵ₀ ≤ Module.rank K V) :
    Module.rank K V < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  convert! lift_rank_lt_rank_dual' h; rw [lift_id]
/-
**rank_lt_rank_dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_lt_rank_dual {K V : Type u} [Field K] [AddCommGroup V] [Module K V] (
h : ℵ₀ <= Module.rank K V) : Module.rank K V < Module.rank K (V ->ₗ[K] K)
参数：h : ℵ₀ <= Module.rank K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_lt_rank_dual`：lift_rank_lt_rank_dual {K : Type u} {V : Type v}
 [Field K] [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank K V) : Cardinal.
lift.{u} (Mo…
-/
theorem rank_lt_rank_dual {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K V < Module.rank K (V →ₗ[K] K) := by
  convert! lift_rank_lt_rank_dual h; rw [lift_id]

end Cardinal

