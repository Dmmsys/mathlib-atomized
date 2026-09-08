/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!

# Topological monoids with open units

We say that a topological monoid `M` has open units (`IsOpenUnits`) if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)` (`IsOpenUnits.of_isAdic`).

A non-example is `𝔸ₖ`, because the topology on ideles is not the induced topology from adeles.

This condition is necessary and sufficient for `U(R)` to be an open subspace of `X(R)`
for all affine scheme `X` over `R` and all affine open subscheme `U ⊆ X`.
-/

public section

open Topology

/--
We say that a topological monoid `M` has open units if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)`.
-/
@[mk_iff]
/-
**IsOpenUnits** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Monoid M] → [TopologicalSpace M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a topological monoid `M` has open units if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or 
fields),
and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)`.
-/
class IsOpenUnits (M : Type*) [Monoid M] [TopologicalSpace M] : Prop where
  isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Mˣ → M)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (M : Type*) [Monoid M] [TopologicalSpace M] [DiscreteTopology M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal :=
    .of_continuous_injective_isOpenMap Units.continuous_val Units.val_injective
      fun _ _ ↦ isOpen_discrete _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {M : Type*} [Group M] [TopologicalSpace M] [ContinuousInv M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal := toUnits_homeomorph.symm.isOpenEmbedding
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {M : Type*} [GroupWithZero M]
    [TopologicalSpace M] [ContinuousInv₀ M] [T1Space M] : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    convert! (isClosed_singleton (X := M) (x := 0)).isOpen_compl
    ext
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact isUnit_iff_ne_zero

/-- If `R` has the `I`-adic topology where `I` is contained in the Jacobson radical
(e.g. when `R` is complete or local), then `Rˣ` is an open subspace of `R`. -/
/-
**IsOpenUnits.of_isAdic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpenUnits.of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R] [IsTop
ologicalRing R] {I : Ideal R} (hR : IsAdic I) (hI : I <= Ideal.jacobson ⊥) : IsO
penUnits R
参数：hR : IsAdic I；hI : I <= Ideal.jacobson ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `Units.continuous_val`：continuous_val : Continuous ((↑) : Mˣ -> M)
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsTopologicalGroup.isOpenMap_iff_nhds_one`：IsTopologicalGroup.isOpenMap_
iff_nhds_one {H : Type*} [Monoid H] [TopologicalSpace H] [ContinuousConstSMul H 
H] {F : Type*} [FunLike F G H] …
· 使用定理 `Units.instIsTopologicalGroupOfContinuousMul`：∀ {α : Type u} [inst : Mono
id α] [inst_1 : TopologicalSpace α] [ContinuousMul α], IsTopologicalGroup αˣ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Units.embedProduct_apply`：∀ (α : Type u_6) [inst : Monoid α] (x : αˣ), (
Units.embedProduct α) x = (↑x, MulOpposite.op ↑x⁻¹)
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.hasBasis_nhds_adic`：hasBasis_nhds_adic (I : Ideal R) (x : R) : Has
Basis (@nhds R I.adicTopology x) (fun _n : Nat => True) fun n => (fun y => x + y
) '' (I ^ n : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulOpposite.opHomeomorph_symm_apply`：∀ {M : Type u_1} [inst : Topologica
lSpace M] (a : Mᵐᵒᵖ), MulOpposite.opHomeomorph.symm a = MulOpposite.unop a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If `R` has the `I`-adic topology where `I` is contained in the Jacobson radical
(e.g. when `R` is complete or local), then `Rˣ` is an open subspace of `R`.
-/
lemma IsOpenUnits.of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {I : Ideal R}
    (hR : IsAdic I) (hI : I ≤ Ideal.jacobson ⊥) :
    IsOpenUnits R := by
  refine ⟨.of_continuous_injective_isOpenMap Units.continuous_val Units.val_injective ?_⟩
  refine (IsTopologicalGroup.isOpenMap_iff_nhds_one (f := Units.coeHom R)).mpr ?_
  rw [nhds_induced, nhds_prod_eq]
  simp only [Units.embedProduct_apply, Units.val_one, inv_one, MulOpposite.op_one]
  intro s hs
  have H := hR ▸ Ideal.hasBasis_nhds_adic I 1
  have := (H.prod (H.comap MulOpposite.opHomeomorph.symm))
  simp only [Homeomorph.comap_nhds_eq, Homeomorph.symm_symm, MulOpposite.opHomeomorph_apply,
    MulOpposite.op_one, and_self, Set.image_add_left] at this
  have : ∃ n₁ n₂, ∀ (u : Rˣ), (-1 + u : R) ∈ I ^ n₁ → (-1 + u⁻¹ : R) ∈ I ^ n₂ → ↑u ∈ s := by
    simpa [Set.subset_def, forall_comm (β := Rˣ), forall_comm (β := _ = _)] using
      (((this.comap (Units.embedProduct R)).map (Units.coeHom R)).1 _).mp hs
  obtain ⟨n, hn, hn'⟩ : ∃ n ≠ 0, ∀ (u : Rˣ), (-1 + u : R) ∈ I ^ n →
      (-1 + u⁻¹ : R) ∈ I ^ n → ↑u ∈ s := by
    obtain ⟨n₁, n₂, H⟩ := this
    exact ⟨n₁ ⊔ n₂ ⊔ 1, by simp, fun u h₁ h₂ ↦ H u
      (Ideal.pow_le_pow_right (by simp) h₁)
      (Ideal.pow_le_pow_right (by simp) h₂)⟩
  rw [H.1]
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := Ideal.mem_jacobson_bot.mp (hI (Ideal.pow_le_self hn hx)) 1
  rw [mul_one, add_comm] at this
  refine hn' this.unit (by simpa using hx) ?_
  have : -1 + ↑this.unit⁻¹ = -this.unit⁻¹ * x := by
    trans this.unit⁻¹ * (-(1 + x) + 1)
    · rw [mul_add, mul_neg, IsUnit.val_inv_mul, mul_one]
    · simp
  rw [this]
  exact Ideal.mul_mem_left _ _ hx
