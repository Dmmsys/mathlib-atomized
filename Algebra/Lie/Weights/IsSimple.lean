/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Lie ideals, invariant root submodules, and simple Lie algebras

Given a semisimple Lie algebra, the lattice of ideals is order isomorphic to the lattice of
Weyl-group-invariant submodules of the corresponding root system. In this file we provide
`LieIdeal.toInvtRootSubmodule`, which constructs the invariant submodule associated to an ideal,
and `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`, which constructs the ideal associated to an
invariant submodule.

## Main definitions
* `LieIdeal.rootSet`: the set of roots whose root space is contained in a given Lie ideal.
* `LieIdeal.rootSpan`: the submodule of `Dual K H` spanned by `LieIdeal.rootSet`.
* `LieIdeal.toInvtRootSubmodule`: the invariant root submodule associated to an ideal.
* `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant
  submodule of the dual space.
* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.

## Main results
* `LieAlgebra.IsKilling.restr_inf_cartan_eq_iSup_corootSubmodule`: the intersection of a Lie ideal
  and a Cartan subalgebra is the span of the coroots whose roots have root spaces in the ideal.
* `LieAlgebra.IsKilling.isSimple_iff_isIrreducible`: a Killing Lie algebra is simple if and only
  if its root system is irreducible.
-/

@[expose] public section

namespace LieIdeal

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-
**LieIdeal.corootSubmodule_le** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：corootSubmodule_le (I : LieIdeal K L) {α : Weight K H L} (hα : rootSpace H
 α <= I.restr H) : corootSubmodule α <= I.restr H
参数：I : LieIdeal K L；hα : rootSpace H α <= I.restr H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.mem_map`：mem_map (m' : M') : m' in N.map f ↔ exists m, m in
 N ∧ f m = m'
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `lie_mem_left`：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅
x, y⁆ in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.mem_corootSpace`：mem_corootSpace {x : H} : x in corootSpace α
 ↔ (x : L) in Submodule.span R {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H 
(-α))}
-/
lemma corootSubmodule_le (I : LieIdeal K L) {α : Weight K H L}
    (hα : rootSpace H α ≤ I.restr H) :
    corootSubmodule α ≤ I.restr H := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨a.val, a.property⟩ : H) ∈ corootSpace α := ha
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

/-- The set of roots whose root space is contained in a given Lie ideal. -/
/-
**LieIdeal.rootSet** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：rootSet (I : LieIdeal K L) : Set H.root
参数：I : LieIdeal K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of roots whose root space is contained in a given Lie ideal.
-/
def rootSet (I : LieIdeal K L) : Set H.root := { α | rootSpace H α.1 ≤ I.restr H }
/-
**LieIdeal.mem_rootSet** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：mem_rootSet {I : LieIdeal K L} {α : H.root} : α in I.rootSet ↔ rootSpace H
 α.1 <= I.restr H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_rootSet {I : LieIdeal K L} {α : H.root} :
    α ∈ I.rootSet ↔ rootSpace H α.1 ≤ I.restr H := Iff.rfl

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal. -/
/-
**LieIdeal.rootSpan** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：rootSpan (I : LieIdeal K L) : Submodule K (Dual K H)
参数：I : LieIdeal K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of `Dual K H` spanned by the roots associated to a Lie ideal.
-/
noncomputable def rootSpan (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((rootSystem H).root '' I.rootSet)
/-
**LieIdeal.rootSpace_le_of_apply_coroot_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieId
eal`。
形式化陈述：rootSpace_le_of_apply_coroot_ne_zero (I : LieIdeal K L) {α : Weight K H L}
 (hα : rootSpace H α <= I.restr H) {γ : H -> K} (hγ_ne : γ (coroot α) != 0) : ro
otSpace H γ <= I.restr H
参数：I : LieIdeal K L；hα : rootSpace H α <= I.restr H；hγ_ne : γ (coroot α) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace`：lie_eq_smul_of_mem_ro
otSpace {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H) : ⁅h, x⁆ = α h • 
x
· 使用定理 `lie_mem_left`：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅
x, y⁆ in I
· 使用引理 `LieIdeal.corootSubmodule_le`：corootSubmodule_le (I : LieIdeal K L) {α : 
Weight K H L} (hα : rootSpace H α <= I.restr H) : corootSubmodule α <= I.restr H
· 使用引理 `LieAlgebra.IsKilling.coe_coroot_mem_corootSubmodule`：coe_coroot_mem_coro
otSubmodule (α : Weight K H L) : (coroot α : L) in corootSubmodule α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
-/
lemma rootSpace_le_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hα : rootSpace H α ≤ I.restr H)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    rootSpace H γ ≤ I.restr H := by
  intro y hy
  have : γ (coroot α) • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule α))
  exact I.toSubmodule.smul_mem_iff hγ_ne |>.mp this
/-
**LieIdeal.reflectionPerm_mem_rootSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：reflectionPerm_mem_rootSet_iff (I : LieIdeal K L) (α β : H.root) : (rootSy
stem H).reflectionPerm β α in I.rootSet ↔ α in I.rootSet
参数：I : LieIdeal K L；α β : H.root。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.reflectionPerm_eq_of_pairing_eq_zero`：reflectionPerm_eq_of_p
airing_eq_zero (h : P.pairing j i = 0) : P.reflectionPerm i j = j
· 使用引理 `LieIdeal.rootSpace_le_of_apply_coroot_ne_zero`：rootSpace_le_of_apply_cor
oot_ne_zero (I : LieIdeal K L) {α : Weight K H L} (hα : rootSpace H α <= I.restr
 H) {γ : H -> K} (hγ_ne : γ (coroot…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `LinearMap.instIsTorsionFree`：∀ {R : Type u_1} {R' : Type u_2} {S : Type 
u_3} {M : Type u_4} {M' : Type u_5} [inst : Semiring R]   [inst_1 : Semiring R']
 [inst_2 : AddCom…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.pairing_reflectionPerm`：pairing_reflectionPerm (i j k : ι) :
 P.pairing j (P.reflectionPerm i k) = P.pairing (P.reflectionPerm i j) k
· 使用引理 `RootPairing.pairing_reflectionPerm_self_right`：pairing_reflectionPerm_se
lf_right (i j : ι) : P.pairing i (P.reflectionPerm j j) = - P.pairing i j
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `RootPairing.reflectionPerm_self`：reflectionPerm_self : P.reflectionPerm 
i (P.reflectionPerm i j) = j
-/
lemma reflectionPerm_mem_rootSet_iff (I : LieIdeal K L) (α β : H.root) :
    (rootSystem H).reflectionPerm β α ∈ I.rootSet ↔ α ∈ I.rootSet := by
  let S := rootSystem H
  suffices h : ∀ γ δ : H.root, δ ∈ I.rootSet → S.reflectionPerm γ δ ∈ I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := I.rootSpace_le_of_apply_coroot_ne_zero hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ ≠ 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact I.rootSpace_le_of_apply_coroot_ne_zero hγ h_neg

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
/-
**LieIdeal.rootSpan_mem_invtRootSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：rootSpan_mem_invtRootSubmodule (I : LieIdeal K L) : I.rootSpan in (rootSys
tem H).invtRootSubmodule
参数：I : LieIdeal K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.mem_invtRootSubmodule_iff`：mem_invtRootSubmodule_iff {q : Su
bmodule R M} : q in P.invtRootSubmodule ↔ forall i, q in Module.End.invtSubmodul
e (P.reflection i)
· 使用引理 `Module.End.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule R M} : p 
in f.invtSubmodule ↔ p <= p.comap f
· 使用定理 `LieIdeal.rootSpan.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K]
 [inst_1 : LieRing L] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K 
L] {H : LieS…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LieIdeal.reflectionPerm_mem_rootSet_iff`：reflectionPerm_mem_rootSet_iff 
(I : LieIdeal K L) (α β : H.root) : (rootSystem H).reflectionPerm β α in I.rootS
et ↔ α in I.rootSet

--- 原说明 ---
The submodule spanned by roots of a Lie ideal is invariant under all root reflec
tions.
-/
lemma rootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    I.rootSpan ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule, rootSpan, Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (I.reflectionPerm_mem_rootSet_iff α β).mpr hα, rfl⟩

/-- The invariant root submodule corresponding to a Lie ideal.

Given a Lie ideal `I`, this produces an invariant root submodule by taking the span of all
roots whose root spaces are contained in `I`. -/
/-
**LieIdeal.toInvtRootSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：toInvtRootSubmodule (I : LieIdeal K L) : (rootSystem H).invtRootSubmodule
参数：I : LieIdeal K L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LieIdeal.rootSpan_mem_invtRootSubmodule`：rootSpan_mem_invtRootSubmodule 
(I : LieIdeal K L) : I.rootSpan in (rootSystem H).invtRootSubmodule

--- 原说明 ---
The invariant root submodule corresponding to a Lie ideal.

Given a Lie ideal `I`, this produces an invariant root submodule by taking the s
pan of all
roots whose root spaces are contained in `I`.
-/
noncomputable def toInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨I.rootSpan, I.rootSpan_mem_invtRootSubmodule⟩

@[gcongr]
/-
**LieIdeal.toInvtRootSubmodule_mono** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：toInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I <= J) : I.toInvtRootS
ubmodule (H
参数：h : I <= J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma toInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    I.toInvtRootSubmodule (H := H) ≤ J.toInvtRootSubmodule :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 ≤ I.restr H) ↦ hα.trans (show I.restr H ≤ J.restr H from h))
/-
**LieIdeal.root_apply_eq_zero_of_notMem_rootSet** 是 Mathlib 中的一个引理，位于命名空间 `LieId
eal`。
形式化陈述：root_apply_eq_zero_of_notMem_rootSet (I : LieIdeal K L) {h : H} (hI : (h :
 L) in I) {β : H.root} (hβ : β ∉ I.rootSet) : (β : Weight K H L) h = 0
参数：I : LieIdeal K L；hI : (h : L) in I；hβ : β ∉ I.rootSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace`：lie_eq_smul_of_mem_ro
otSpace {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H) : ⁅h, x⁆ = α h • 
x
· 使用定理 `lie_mem_left`：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅
x, y⁆ in I
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
-/
lemma root_apply_eq_zero_of_notMem_rootSet (I : LieIdeal K L)
    {h : H} (hI : (h : L) ∈ I) {β : H.root} (hβ : β ∉ I.rootSet) :
    (β : Weight K H L) h = 0 := by
  simp only [LieIdeal.mem_rootSet] at hβ
  contrapose! hβ
  intro y hy
  have h_smul : (β : Weight K H L) h • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy h]
    exact lie_mem_left K L I h y hI
  rwa [I.toSubmodule.smul_mem_iff hβ] at h_smul
/-
**LieIdeal.rootSet_apply_coroot_eq_zero_of_notMem_rootSet** 是 Mathlib 中的一个引理，位于命
名空间 `LieIdeal`。
形式化陈述：rootSet_apply_coroot_eq_zero_of_notMem_rootSet (I : LieIdeal K L) {α : H.r
oot} (hα : α in I.rootSet) {β : H.root} (hβ : β ∉ I.rootSet) : (α : Weight K H L
) (coroot β) = 0
参数：I : LieIdeal K L；hα : α in I.rootSet；hβ : β ∉ I.rootSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `LieIdeal.root_apply_eq_zero_of_notMem_rootSet`：root_apply_eq_zero_of_not
Mem_rootSet (I : LieIdeal K L) {h : H} (hI : (h : L) in I) {β : H.root} (hβ : β 
∉ I.rootSet) : (β : Weight K H L) h…
· 使用引理 `LieIdeal.corootSubmodule_le`：corootSubmodule_le (I : LieIdeal K L) {α : 
Weight K H L} (hα : rootSpace H α <= I.restr H) : corootSubmodule α <= I.restr H
· 使用引理 `LieAlgebra.IsKilling.coe_coroot_mem_corootSubmodule`：coe_coroot_mem_coro
otSubmodule (α : Weight K H L) : (coroot α : L) in corootSubmodule α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.IsKilling.orthogonal_span_coroot_eq_ker`：∀ {K : Type u_2} {L 
: Type u_3} [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [i
nst_3 : FiniteDimensional K L] {H : LieS…
· 使用定理 `LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker`：orthogonal_s
pan_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) : B.orthogonal (K ∙ x) = 
LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ …
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用引理 `LieAlgebra.IsKilling.traceForm_eq_zero_of_mem_ker_of_mem_span_coroot`：tr
aceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : H} (hx :
 x in α.ker) (hy : y in K ∙ coroot α) : traceForm K H L x …
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
-/
lemma rootSet_apply_coroot_eq_zero_of_notMem_rootSet (I : LieIdeal K L)
    {α : H.root} (hα : α ∈ I.rootSet)
    {β : H.root} (hβ : β ∉ I.rootSet) :
    (α : Weight K H L) (coroot β) = 0 := by
  have h_ker : coroot (α : Weight K H L) ∈ (β : Weight K H L).ker :=
    I.root_apply_eq_zero_of_notMem_rootSet
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule _)) hβ
  change coroot (β : Weight K H L) ∈ (α : Weight K H L).ker
  rw [← orthogonal_span_coroot_eq_ker,
    LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker, LinearMap.mem_ker]
  exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot h_ker (Submodule.mem_span_singleton_self _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The intersection of a Lie ideal and a Cartan subalgebra is the span of the coroots whose roots
have root spaces in the ideal. -/
/-
**LieIdeal.restr_inf_cartan_eq_biSup_corootSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `
LieIdeal`。
形式化陈述：restr_inf_cartan_eq_biSup_corootSubmodule (I : LieIdeal K L) : I.restr H ⊓
 H.toLieSubmodule = ⨆ α in I.rootSet, corootSubmodule α.1
参数：I : LieIdeal K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_split`：iSup_split (f : β -> α) (p : β -> Prop) : ⨆ i, f i = (⨆ (i) 
(_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `LieAlgebra.IsKilling.biSup_corootSpace_eq_top`：biSup_corootSpace_eq_top 
: ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.map_iSup`：map_iSup {ι : Sort*} (N : ι -> LieSubmodule R L M
) : (⨆ i, N i).map f = ⨆ i, (N i).map f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton`：coe_corootSpace_
eq_span_singleton (α : Weight K H L) : (corootSpace α).toSubmodule = K ∙ coroot 
α
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用引理 `LieIdeal.rootSet_apply_coroot_eq_zero_of_notMem_rootSet`：rootSet_apply_c
oroot_eq_zero_of_notMem_rootSet (I : LieIdeal K L) {α : H.root} (hα : α in I.roo
tSet) {β : H.root} (hβ : β ∉ I.rootSet) : (α …
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The intersection of a Lie ideal and a Cartan subalgebra is the span of the coroo
ts whose roots
have root spaces in the ideal.
-/
lemma restr_inf_cartan_eq_biSup_corootSubmodule (I : LieIdeal K L) :
    I.restr H ⊓ H.toLieSubmodule = ⨆ α ∈ I.rootSet, corootSubmodule α.1 := by
  refine le_antisymm ?_ (iSup₂_le fun _ hα ↦
    le_inf (I.corootSubmodule_le hα) LieSubmodule.map_incl_le)
  intro x ⟨hxI, hxH⟩
  let f : H.root → LieIdeal K H := fun α ↦ corootSpace α.1
  set span_I_roots := ⨆ α ∈ I.rootSet, f α
  set span_compl_roots := ⨆ (β : H.root) (_ : β ∉ I.rootSet), f β
  have h_split : span_I_roots ⊔ span_compl_roots = ⨆ α, f α :=
    (iSup_split f (· ∈ I.rootSet)).symm
  have h_top : span_I_roots ⊔ span_compl_roots = ⊤ := by
    rw [h_split, eq_top_iff, ← biSup_corootSpace_eq_top]
    exact iSup₂_le fun α hα ↦ le_iSup_of_le ⟨α, by simpa [LieSubalgebra.root] using hα⟩ le_rfl
  have hspan_I_roots_incl : LieSubmodule.map H.toLieSubmodule.incl span_I_roots =
      ⨆ α ∈ I.rootSet, corootSubmodule α.1 := by
    change LieSubmodule.map _ (⨆ α ∈ I.rootSet, f α) = ⨆ α ∈ I.rootSet, _
    simp_rw [LieSubmodule.map_iSup]; rfl
  have hspan_compl_roots_vanish (μ : H.root) (hμ : μ ∈ I.rootSet) :
      span_compl_roots.toSubmodule ≤ μ.1.ker := by
    have : span_compl_roots.toSubmodule = ⨆ β ∉ I.rootSet, (f β).toSubmodule := by
      simp_rw [span_compl_roots, LieSubmodule.iSup_toSubmodule]
    rw [this]
    exact iSup₂_le fun γ hγ ↦ by
      rw [coe_corootSpace_eq_span_singleton, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hμ hγ
  have hx_top : (⟨x, hxH⟩ : H) ∈ span_I_roots ⊔ span_compl_roots := h_top ▸ trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx_top
  have haI : (a : L) ∈ I :=
    (iSup₂_le (fun _ hα ↦ I.corootSubmodule_le hα) :
      ⨆ α ∈ I.rootSet, corootSubmodule α.1 ≤ _)
      (hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha)
  have hbI : (b : L) ∈ I := by
    have h_sum : (a : L) + b = x := congr_arg Subtype.val hab
    have h_b_eq : (b : L) = x - a := by rw [← h_sum, add_sub_cancel_left]
    rw [h_b_eq]; exact I.toSubmodule.sub_mem hxI haI
  suffices b = 0 by
    subst this; simp only [add_zero] at hab; subst hab
    exact hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha
  suffices b ∈ ⨅ α : Weight K H L, α.ker by simpa [iInf_ker_weight_eq_bot] using this
  refine (Submodule.mem_iInf _).mpr fun μ ↦ ?_
  by_cases hμ : μ.IsNonZero
  · have hμ_root : μ ∈ H.root := by simpa [LieSubalgebra.root] using hμ
    by_cases hμI : (⟨μ, hμ_root⟩ : H.root) ∈ I.rootSet
    · exact hspan_compl_roots_vanish ⟨μ, hμ_root⟩ hμI hb
    · exact I.root_apply_eq_zero_of_notMem_rootSet hbI hμI
  · simp only [Weight.IsNonZero, not_not] at hμ
    exact LinearMap.mem_ker.mpr (congr_fun hμ b)
/-
**LieIdeal.mem_rootSet_of_mem_rootSpan** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：mem_rootSet_of_mem_rootSpan (I : LieIdeal K L) {α : H.root} (hα_span : (α 
: Dual K H) in I.rootSpan) : α in I.rootSet
参数：I : LieIdeal K L；hα_span : (α : Dual K H) in I.rootSpan。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LieSubalgebra.isNonZero_coe_root`：∀ {K : Type u_2} {L : Type u_3} [inst 
: LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDime
nsional K L] {H : LieS…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.rootSpan.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K]
 [inst_1 : LieRing L] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K 
L] {H : LieS…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LieIdeal.rootSet_apply_coroot_eq_zero_of_notMem_rootSet`：rootSet_apply_c
oroot_eq_zero_of_notMem_rootSet (I : LieIdeal K L) {α : H.root} (hα : α in I.roo
tSet) {β : H.root} (hβ : β ∉ I.rootSet) : (α …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
-/
lemma mem_rootSet_of_mem_rootSpan (I : LieIdeal K L)
    {α : H.root} (hα_span : (α : Dual K H) ∈ I.rootSpan) :
    α ∈ I.rootSet := by
  by_contra hα_not
  have hα_nz := H.isNonZero_coe_root α
  have : I.rootSpan ≤ LinearMap.ker (Dual.eval K H (coroot (α : Weight K H L))) := by
    rw [LieIdeal.rootSpan, Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (this hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero
/-
**LieIdeal.restr_eq_iSup_sl2SubmoduleOfRoot** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`
。
形式化陈述：restr_eq_iSup_sl2SubmoduleOfRoot (I : LieIdeal K L) : I.restr H = ⨆ (α : H
.root) (_ : α in I.rootSet), sl2SubmoduleOfRoot (H.isNonZero_coe_root α)
参数：I : LieIdeal K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LieSubalgebra.isNonZero_coe_root`：∀ {K : Type u_2} {L : Type u_3} [inst 
: LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDime
nsional K L] {H : LieS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`：lieIdea
l_eq_inf_cartan_sup_biSup_rootSpace (I : LieIdeal K L) : I.restr H = (I.restr H 
⊓ H.toLieSubmodule) ⊔ ⨆ (α : H.root) (_ : rootSpace H…
· 使用引理 `LieIdeal.restr_inf_cartan_eq_biSup_corootSubmodule`：restr_inf_cartan_eq_
biSup_corootSubmodule (I : LieIdeal K L) : I.restr H ⊓ H.toLieSubmodule = ⨆ α in
 I.rootSet, corootSubmodule α.1
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup`：sl2SubmoduleOfRoot_eq_su
p (α : Weight K H L) (hα : α.IsNonZero) : sl2SubmoduleOfRoot hα = genWeightSpace
 L α ⊔ genWeightSpace L (-α) ⊔ coroo…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用引理 `LieIdeal.rootSpace_le_of_apply_coroot_ne_zero`：rootSpace_le_of_apply_cor
oot_ne_zero (I : LieIdeal K L) {α : Weight K H L} (hα : rootSpace H α <= I.restr
 H) {γ : H -> K} (hγ_ne : γ (coroot…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `LieIdeal.corootSubmodule_le`：corootSubmodule_le (I : LieIdeal K L) {α : 
Weight K H L} (hα : rootSpace H α <= I.restr H) : corootSubmodule α <= I.restr H
-/
lemma restr_eq_iSup_sl2SubmoduleOfRoot (I : LieIdeal K L) :
    I.restr H =
      ⨆ (α : H.root) (_ : α ∈ I.rootSet), sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
  apply le_antisymm
  · rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, restr_inf_cartan_eq_biSup_corootSubmodule]
    apply sup_le
    · exact iSup₂_le fun β hβ ↦ le_iSup₂_of_le β hβ
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα ↦ le_iSup₂_of_le α hα
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)
  · exact iSup₂_le fun α hα ↦ by
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact hα
      · apply I.rootSpace_le_of_apply_coroot_ne_zero hα
        simp [Pi.neg_apply, root_apply_coroot (H.isNonZero_coe_root α)]
      · exact I.corootSubmodule_le hα

end LieIdeal

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

section aux

variable (q : Submodule K (Dual K H))
  (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i))
  (χ : Weight K H L)
  (x_χ m_α : L) (hx_χ : x_χ ∈ genWeightSpace L χ)
  (α : Weight K H L) (hαq : ↑α ∈ q) (hα₀ : α.IsNonZero)

section

variable
  (w_plus : χ.toLinear + α.toLinear ≠ 0)
  (w_minus : χ.toLinear - α.toLinear ≠ 0)
  (w_chi : χ.toLinear ≠ 0)
  (m_pos m_neg : L)
  (y : H) (hy : y ∈ corootSpace α)
  (h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, (y : L)⁆)
  (h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (⇑χ + ⇑α))
  (h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (⇑χ - ⇑α))

include hx_χ w_plus w_minus w_chi h_bracket_sum h_pos_containment h_neg_containment hαq

/-
**LieAlgebra.IsKilling.chi_in_q_aux** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.IsKill
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem chi_in_q_aux (h_chi_in_q : ↑χ ∈ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have h_h_containment : ⁅x_χ, (y : L)⁆ ∈ genWeightSpace L χ := by
    have h_zero_weight : H.toLieSubmodule.incl y ∈ genWeightSpace L (0 : H → K) := by
      apply toLieSubmodule_le_rootSpace_zero
      exact y.property
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
    ext h; simp
  have h_bracket_decomp : ⁅x_χ, m_α⁆ ∈
      genWeightSpace L (χ.toLinear + α.toLinear) ⊔
      genWeightSpace L (χ.toLinear - α.toLinear) ⊔ genWeightSpace L χ := by
    rw [h_bracket_sum]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
      (Submodule.mem_sup_right h_h_containment)
  let I := ⨆ β : {β : Weight K H L // ↑β ∈ q ∧ β.IsNonZero}, sl2SubmoduleOfRoot β.2.2
  have genWeightSpace_le_I (β_lin : H →ₗ[K] K) (hβ_in_q : β_lin ∈ q)
      (hβ_ne_zero : β_lin ≠ 0) : genWeightSpace L β_lin ≤ I := by
    by_cases h_trivial : genWeightSpace L β_lin = ⊥
    · simp [h_trivial]
    · let β : Weight K H L := ⟨β_lin, h_trivial⟩
      have hβ_nonzero : β.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp hβ_ne_zero
      refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have h_plus_contain : genWeightSpace L (χ.toLinear + α.toLinear) ≤ I :=
    genWeightSpace_le_I _ (q.add_mem h_chi_in_q hαq) w_plus
  have h_minus_contain : genWeightSpace L (χ.toLinear - α.toLinear) ≤ I :=
    genWeightSpace_le_I _ (by
      have : -α.toLinear = (-1 : K) • α.toLinear := by simp
      rw [sub_eq_add_neg, this]
      exact q.add_mem h_chi_in_q (q.smul_mem (-1) hαq)) w_minus
  have h_chi_contain : genWeightSpace L χ.toLinear ≤ I :=
    genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
  exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp

include hq hα₀ hy
/-
**LieAlgebra.IsKilling.chi_not_in_q_aux** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Is
Killing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem chi_not_in_q_aux (h_chi_not_in_q : ↑χ ∉ q) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  let S := rootSystem H
  have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) : ∃ i, S.root i = ↑γ :=
    ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by rw [hj]; exact hαq))
  have h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥ := by
    by_contra h_minus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear - α.toLinear, h_minus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_minus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index (-α) (Weight.IsNonZero.neg hα₀)
    have h_sum_in_range : S.root i + S.root j ∈ Set.range S.root := by
      rw [hi, hj, Weight.toLinear_neg, ← sub_eq_add_neg]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by
      rw [hj, Weight.toLinear_neg]
      convert q.smul_mem (-1) hαq
      rw [neg_smul, one_smul]))
  obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
  obtain ⟨j, hj⟩ := exists_root_index α hα₀
  have h_pairing_zero : S.pairing i j = 0 := by
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S
    · intro h_eq; exact w_minus (by rw [← hi, ← hj, h_eq, sub_self])
    · intro h_eq; exact w_plus (by rw [← hi, ← hj, h_eq, neg_add_cancel])
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) ≠ ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx, hi, hj] at this
      exact this h_plus_bot
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) ≠ ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx, hi, hj] at this
      exact this h_minus_bot
  have h_pos_zero : ⁅x_χ, m_pos⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_pos⁆ ∈ (⊥ : LieSubmodule K H L) := by
      rw [← h_plus_bot]
      exact h_pos_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_neg_zero : ⁅x_χ, m_neg⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_neg⁆ ∈ (⊥ : LieSubmodule K H L) := by
      rw [← h_minus_bot]
      exact h_neg_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_bracket_zero : ⁅x_χ, (y : L)⁆ = 0 := by
    have h_chi_coroot_zero : χ (coroot α) = 0 := by
      have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
        rw [rootSystem_pairing_apply]
      rw [h_pairing_zero] at h_pairing_eq
      have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
        apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
      have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
      have hj_val : j.1 = α := w_eq (by rw [← hj]; rfl)
      rw [hi_val, hj_val] at h_pairing_eq
      exact h_pairing_eq.symm
    have h_lie_eq_smul : ⁅(y : L), x_χ⁆ = χ y • x_χ := lie_eq_smul_of_mem_rootSpace hx_χ y
    have h_chi_h_zero : χ y = 0 := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| by
        rw [← coe_corootSpace_eq_span_singleton α, LieSubmodule.mem_toSubmodule]
        exact hy
      rw [← hc, map_smul, h_chi_coroot_zero, smul_zero]
    have h_bracket_elem : ⁅x_χ, (y : L)⁆ = 0 := by
      rw [← lie_skew, h_lie_eq_smul, h_chi_h_zero, zero_smul, neg_zero]
    exact h_bracket_elem
  rw [h_bracket_sum, h_pos_zero, h_neg_zero, h_bracket_zero]
  simp only [add_zero, zero_mem]

end

set_option backward.isDefEq.respectTransparency.types false in
include hq hx_χ hαq in
/-
**LieAlgebra.IsKilling.invtSubmoduleToLieIdeal_aux** 是 Mathlib 中的一个定理，位于命名空间 `Li
eAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem invtSubmoduleToLieIdeal_aux (hm_α : m_α ∈ sl2SubmoduleOfRoot hα₀) :
    ⁅x_χ, m_α⁆ ∈ ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have hm_α_original : m_α ∈ sl2SubmoduleOfRoot hα₀ := hm_α
  rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
  obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
  obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg
  have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
    rw [← hm_eq, ← hm_αneg_eq]
  have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
    rw [hm_α_decomp, lie_add, lie_add]
  by_cases w_plus : χ.toLinear + α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_neg : x_χ ∈ genWeightSpace L (-α.toLinear) := by
        rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
        (finrank_rootSpace_eq_one (-α) (by simpa using hα₀)) ⟨x_χ, hx_χ_neg⟩
      exact ⟨0, c, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_minus : χ.toLinear - α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ ∈ sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_pos : x_χ ∈ genWeightSpace L α.toLinear := by
        rw [← (sub_eq_zero.mp w_minus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
        (finrank_rootSpace_eq_one α hα₀) ⟨x_χ, hx_χ_pos⟩
      exact ⟨c, 0, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_chi : χ.toLinear = 0
  · have hx_χ_in_H : x_χ ∈ H.toLieSubmodule := by
      rw [← rootSpace_zero_eq K L H]
      convert! hx_χ; ext h; simp only [Pi.zero_apply]
      have h_apply : (χ.toLinear : H → K) h = 0 := by rw [w_chi, LinearMap.zero_apply]
      exact h_apply.symm
    apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    rw [← (by rfl : ⁅(⟨x_χ, hx_χ_in_H⟩ : H), m_α⁆ = ⁅x_χ, m_α⁆)]
    exact (sl2SubmoduleOfRoot hα₀).lie_mem hm_α_original
  have h_pos_containment : ⁅x_χ, m_pos⁆ ∈ genWeightSpace L (χ.toLinear + α.toLinear) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos
  have h_neg_containment : ⁅x_χ, m_neg⁆ ∈ genWeightSpace L (χ.toLinear - α.toLinear) := by
    rw [sub_eq_add_neg]; exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
  obtain ⟨y, hy, rfl⟩ := hm_h
  by_cases h_chi_in_q : ↑χ ∈ q
  · exact chi_in_q_aux q χ x_χ m_α hx_χ α hαq w_plus w_minus w_chi m_pos m_neg y h_bracket_sum
      h_pos_containment h_neg_containment h_chi_in_q
  · exact chi_not_in_q_aux q hq χ x_χ m_α hx_χ α hαq hα₀ w_plus w_minus w_chi m_pos m_neg y hy
      h_bracket_sum h_pos_containment h_neg_containment h_chi_in_q

end aux

/-- Constructs a Lie ideal from an invariant submodule of the dual space of a Cartan subalgebra.

Given a submodule `q` of the dual space `Dual K H` that is invariant under all root reflections,
this produces a Lie ideal by taking the sum of all `sl₂` subalgebras corresponding to roots
whose linear forms lie in `q`. -/
/-
**LieAlgebra.IsKilling.invtSubmoduleToLieIdeal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlg
ebra.IsKilling`。
形式化陈述：invtSubmoduleToLieIdeal (q : Submodule K (Dual K H)) (hq : forall i, q in 
End.invtSubmodule ((rootSystem H).reflection i)) : LieIdeal K L where __
参数：q : Submodule K (Dual K H)；hq : forall i, q in End.invtSubmodule ((rootSystem
 H).reflection i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a Lie ideal from an invariant submodule of the dual space of a Cartan
 subalgebra.

Given a submodule `q` of the dual space `Dual K H` that is invariant under all r
oot reflections,
this produces a Lie ideal by taking the sum of all `sl₂` subalgebras correspondi
ng to roots
whose linear forms lie in `q`.
-/
noncomputable def invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i)) : LieIdeal K L where
  __ := ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2
  lie_mem := by
    intro x m hm
    have hx : x ∈ ⨆ χ : Weight K H L, genWeightSpace L χ := by
      simp [LieModule.iSup_genWeightSpace_eq_top']
    induction hx using LieSubmodule.iSup_induction' with
    | mem χ x_χ hx_χ =>
      induction hm using LieSubmodule.iSup_induction' with
      | mem α m_α hm_α => exact invtSubmoduleToLieIdeal_aux q hq χ x_χ m_α hx_χ α.1 α.2.1 α.2.2 hm_α
      | zero =>
        simp only [Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
    | zero =>
      simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
      exact add_mem ih₁ ih₂
/-
**LieAlgebra.IsKilling.coe_invtSubmoduleToLieIdeal_eq_iSup** 是 Mathlib 中的一个定理，位于
命名空间 `LieAlgebra.IsKilling`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [in
st_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : FiniteDimensional K L] [
inst_5 : LieAlgebra.IsKilling K L] {H : LieSubalgebra K L}   [inst_6 : H.IsCarta
nSubalgebra] [inst_7 : LieModule.IsTriangularizable K (↥H) L] (q : Submodule K (
Module.Dual K ↥H))   (hq : ∀ (i : ↥LieSubalgebra.root), q ∈ Module.End.invtSubmo
dule ↑((LieAlgebra.IsKilling.rootSystem H).reflection i)),   ↑(LieAlgebra.IsKill
ing.invtSubmoduleToLieIdeal q hq) = ↑(⨆ α, LieAlgebra.IsKilling.sl2SubmoduleOfRo
ot ⋯)
参数：↥H；q : Submodule K (Module.Dual K ↥H)；hq : ∀ (i : ↥LieSubalgebra.root), q ∈ M
odule.End.invtSubmodule ↑((LieAlgebra.IsKilling.rootSystem H).reflection i)；LieA
lgebra.IsKilling.invtSubmoduleToLieIdeal q hq；⨆ α, LieAlgebra.IsKilling.sl2Submo
duleOfRoot ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
-/
@[simp] lemma coe_invtSubmoduleToLieIdeal_eq_iSup (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    (invtSubmoduleToLieIdeal q hq).toSubmodule =
      ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 :=
  rfl
/-
**LieAlgebra.IsKilling.restr_invtSubmoduleToLieIdeal_eq_iSup** 是 Mathlib 中的一个定理，
位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [in
st_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : FiniteDimensional K L] [
inst_5 : LieAlgebra.IsKilling K L] {H : LieSubalgebra K L}   [inst_6 : H.IsCarta
nSubalgebra] [inst_7 : LieModule.IsTriangularizable K (↥H) L] (q : Submodule K (
Module.Dual K ↥H))   (hq : ∀ (i : ↥LieSubalgebra.root), q ∈ Module.End.invtSubmo
dule ↑((LieAlgebra.IsKilling.rootSystem H).reflection i)),   LieSubmodule.restr 
(LieAlgebra.IsKilling.invtSubmoduleToLieIdeal q hq) H =     ⨆ α, LieAlgebra.IsKi
lling.sl2SubmoduleOfRoot ⋯
参数：↥H；q : Submodule K (Module.Dual K ↥H)；hq : ∀ (i : ↥LieSubalgebra.root), q ∈ M
odule.End.invtSubmodule ↑((LieAlgebra.IsKilling.rootSystem H).reflection i)；LieA
lgebra.IsKilling.invtSubmoduleToLieIdeal q hq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.restr_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type w}
 [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : 
_root_.Module R M] […
· 使用定理 `LieAlgebra.IsKilling.coe_invtSubmoduleToLieIdeal_eq_iSup`：∀ {K : Type u_
1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [inst_2 : LieRing L] [i
nst_3 : LieAlgebra K L]   [inst_4 : FiniteDime…
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
-/
@[simp] lemma restr_invtSubmoduleToLieIdeal_eq_iSup (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    (invtSubmoduleToLieIdeal q hq).restr H =
      ⨆ α : {α : Weight K H L // ↑α ∈ q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.restr_toSubmodule,
    coe_invtSubmoduleToLieIdeal_eq_iSup, LieSubmodule.iSup_toSubmodule]
/-
**LieAlgebra.IsKilling.mem_rootSet_invtSubmoduleToLieIdeal** 是 Mathlib 中的一个引理，位于
命名空间 `LieAlgebra.IsKilling`。
形式化陈述：mem_rootSet_invtSubmoduleToLieIdeal (q : Submodule K (Dual K H)) (hq : for
all i, q in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) {α : H.
root} : α in (invtSubmoduleToLieIdeal q hq).rootSet ↔ (rootSystem H).root α in q
参数：q : Submodule K (Dual K H)；hq : forall i, q in End.invtSubmodule ((rootSystem
 H).reflection i).toLinearMap。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LieSubalgebra.isNonZero_coe_root`：∀ {K : Type u_2} {L : Type u_3} [inst 
: LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDime
nsional K L] {H : LieS…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup`：sl2SubmoduleOfRoot_eq_su
p (α : Weight K H L) (hα : α.IsNonZero) : sl2SubmoduleOfRoot hα = genWeightSpace
 L α ⊔ genWeightSpace L (-α) ⊔ coroo…
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LieModule.Weight.toLinear_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : L
ieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensi
onal K L] [inst_4 :…
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieSubmodule.map_incl_le`：map_incl_le {N' : LieSubmodule R L N} : N'.map
 N.incl <= N
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用引理 `LieModule.iSupIndep_genWeightSpace`：iSupIndep_genWeightSpace : iSupIndep
 fun χ : L -> R => genWeightSpace M χ
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 37 条，此处仅展示前 30 条）
-/
lemma mem_rootSet_invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) {α : H.root} :
    α ∈ (invtSubmoduleToLieIdeal q hq).rootSet ↔ (rootSystem H).root α ∈ q := by
  set J := invtSubmoduleToLieIdeal q hq
  constructor
  · intro hα_mem
    by_contra hα_not
    have hα_nz := H.isNonZero_coe_root α
    have hne (χ : Weight K H L) (hχ : ↑χ ∈ q) : (χ : H → K) ≠ ((α : Weight K H L) : H → K) :=
      fun heq ↦ hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hχ)
    have h_le : J.restr H ≤ ⨆ (χ : H → K) (_ : χ ≠ (α : Weight K H L)), genWeightSpace L χ := by
      refine iSup_le fun ⟨β, hβ_mem, hβ_nz⟩ ↦ ?_
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂_of_le _ (hne β hβ_mem) le_rfl
      · have : ↑(-β) ∈ q := by rw [Weight.toLinear_neg]; exact q.neg_mem hβ_mem
        exact le_iSup₂_of_le _ (hne (-β) this) le_rfl
      · apply (LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
        exact le_iSup₂_of_le 0 (fun h ↦ hα_nz h.symm) le_rfl
    have h_disj := ((iSupIndep_genWeightSpace K H L _).mono_right h_le).mono_right hα_mem
    exact (α : Weight K H L).genWeightSpace_ne_bot L (disjoint_self.mp h_disj)
  · intro hα
    calc rootSpace H (α : Weight K H L)
        ≤ sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
          rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left
      _ ≤ ⨆ x : {β : Weight K H L // ↑β ∈ q ∧ β.IsNonZero}, sl2SubmoduleOfRoot x.2.2 :=
          le_iSup_of_le ⟨↑α, hα, H.isNonZero_coe_root α⟩ le_rfl
      _ = J.restr H := (restr_invtSubmoduleToLieIdeal_eq_iSup q hq).symm

@[gcongr]
/-
**LieAlgebra.IsKilling.invtSubmoduleToLieIdeal_mono** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)} (hq₁ : foral
l i, q₁ in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) (hq₂ : f
orall i, q₂ in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) (h :
 q₁ <= q₂) : invtSubmoduleToLieIdeal q₁ hq₁ <= invtSubmoduleToLieIdeal q₂ hq₂
参数：Dual K H；hq₁ : forall i, q₁ in End.invtSubmodule ((rootSystem H).reflection i
).toLinearMap；hq₂ : forall i, q₂ in End.invtSubmodule ((rootSystem H).reflection
 i).toLinearMap；h : q₁ <= q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : ∀ i, q₁ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : ∀ i, q₂ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ ≤ q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ ≤ invtSubmoduleToLieIdeal q₂ hq₂ := by
  change (invtSubmoduleToLieIdeal q₁ hq₁).restr H ≤ (invtSubmoduleToLieIdeal q₂ hq₂).restr H
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl
/-
**LieAlgebra.IsKilling.lieIdealOrderIso_left_inv** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra.IsKilling`。
形式化陈述：lieIdealOrderIso_left_inv (I : LieIdeal K L) (hI : forall α, I.rootSpan in
 End.invtSubmodule ((rootSystem H).reflection α).toLinearMap
参数：I : LieIdeal K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.mem_invtRootSubmodule_iff`：mem_invtRootSubmodule_iff {q : Su
bmodule R M} : q in P.invtRootSubmodule ↔ forall i, q in Module.End.invtSubmodul
e (P.reflection i)
· 使用引理 `LieIdeal.rootSpan_mem_invtRootSubmodule`：rootSpan_mem_invtRootSubmodule 
(I : LieIdeal K L) : I.rootSpan in (rootSystem H).invtRootSubmodule
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.mem_rootSet_invtSubmoduleToLieIdeal`：mem_rootSet_in
vtSubmoduleToLieIdeal (q : Submodule K (Dual K H)) (hq : forall i, q in End.invt
Submodule ((rootSystem H).reflection i).toLine…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LieAlgebra.IsKilling.rootSystem_root_apply`：∀ {K : Type u_1} {L : Type u
_2} [inst : Field K] [inst_1 : CharZero K] [inst_2 : LieRing L] [inst_3 : LieAlg
ebra K L]   [inst_4 : LieAlgebra…
· 使用引理 `LieIdeal.mem_rootSet_of_mem_rootSpan`：mem_rootSet_of_mem_rootSpan (I : L
ieIdeal K L) {α : H.root} (hα_span : (α : Dual K H) in I.rootSpan) : α in I.root
Set
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `LieSubalgebra.isNonZero_coe_root`：∀ {K : Type u_2} {L : Type u_3} [inst 
: LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDime
nsional K L] {H : LieS…
· 使用引理 `LieIdeal.restr_eq_iSup_sl2SubmoduleOfRoot`：restr_eq_iSup_sl2SubmoduleOfR
oot (I : LieIdeal K L) : I.restr H = ⨆ (α : H.root) (_ : α in I.rootSet), sl2Sub
moduleOfRoot (H.isNonZero_coe_r…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.restr_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type w}
 [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : 
_root_.Module R M] […
-/
lemma lieIdealOrderIso_left_inv (I : LieIdeal K L)
    (hI : ∀ α, I.rootSpan ∈ End.invtSubmodule ((rootSystem H).reflection α).toLinearMap :=
      (rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule) :
    invtSubmoduleToLieIdeal I.rootSpan hI = I := by
  set J := invtSubmoduleToLieIdeal I.rootSpan
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : ∀ α : H.root, α ∈ J.rootSet ↔ α ∈ I.rootSet := fun α ↦ by
    rw [mem_rootSet_invtSubmoduleToLieIdeal, rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h ↦ Submodule.subset_span ⟨α, h, rfl⟩⟩
  have h_restr : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot, I.restr_eq_iSup_sl2SubmoduleOfRoot]
    exact le_antisymm
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj, ← LieSubmodule.restr_toSubmodule J H,
    ← LieSubmodule.restr_toSubmodule I H, h_restr]
/-
**LieAlgebra.IsKilling.lieIdealOrderIso_right_inv** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Algebra.IsKilling`。
形式化陈述：lieIdealOrderIso_right_inv (q : (rootSystem H).invtRootSubmodule) (hq : fo
rall α, ↑q in End.invtSubmodule ((rootSystem H).reflection α).toLinearMap
参数：q : (rootSystem H).invtRootSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieIdeal.rootSpan_mem_invtRootSubmodule`：rootSpan_mem_invtRootSubmodule 
(I : LieIdeal K L) : I.rootSpan in (rootSystem H).invtRootSubmodule
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.invtRootSubmodule.eq_span_root`：∀ {ι : Type u_1} {M : Type u
_3} {N : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] {K : Type u
_5}   [inst_2 : Field K] [NeZero…
· 使用定理 `LieAlgebra.IsKilling.instIsRootSystemSubtypeWeightMemLieSubalgebraFinset
RootDualRootSystem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : C
harZero K] [inst_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieAlgebra
…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `LieAlgebra.IsKilling.mem_rootSet_invtSubmoduleToLieIdeal`：mem_rootSet_in
vtSubmoduleToLieIdeal (q : Submodule K (Dual K H)) (hq : forall i, q in End.invt
Submodule ((rootSystem H).reflection i).toLine…
-/
lemma lieIdealOrderIso_right_inv (q : (rootSystem H).invtRootSubmodule)
    (hq : ∀ α, ↑q ∈ End.invtSubmodule ((rootSystem H).reflection α).toLinearMap :=
      (rootSystem H).mem_invtRootSubmodule_iff.mp q.property) :
    (invtSubmoduleToLieIdeal q.1 hq).toInvtRootSubmodule = q := by
  simp only [Subtype.ext_iff, LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
  conv_rhs => rw [RootPairing.invtRootSubmodule.eq_span_root q]
  congr 2; ext α
  exact mem_rootSet_invtSubmoduleToLieIdeal _ _

variable (H) in
/-- The order isomorphism between Lie ideals and invariant root submodules. -/
/-
**LieAlgebra.IsKilling.lieIdealOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Is
Killing`。
形式化陈述：lieIdealOrderIso : LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where 
toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism between Lie ideals and invariant root submodules.
-/
noncomputable def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv := lieIdealOrderIso_left_inv
  right_inv := lieIdealOrderIso_right_inv
  map_rel_iff' {I J} := by
    refine ⟨fun h ↦ ?_, LieIdeal.toInvtRootSubmodule_mono⟩
    rw [← lieIdealOrderIso_left_inv (H := H) I, ← lieIdealOrderIso_left_inv (H := H) J]
    exact invtSubmoduleToLieIdeal_mono _ _ h

/-- A Killing Lie algebra is simple if and only if its root system is irreducible. -/
/-
**LieAlgebra.IsKilling.isSimple_iff_isIrreducible** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Algebra.IsKilling`。
形式化陈述：isSimple_iff_isIrreducible : (rootSystem H).IsIrreducible ↔ IsSimple K L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `LieAlgebra.IsKilling.isLieAbelian_iff_subsingleton`：isLieAbelian_iff_sub
singleton [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRi
ng R] : IsLieAbelian L ↔ Subsingleton L
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用引理 `RootPairing.isIrreducible_iff_invtRootSubmodule`：isIrreducible_iff_invtR
ootSubmodule {K : Type*} [Field K] [Module K M] [Module K N] [Nontrivial M] (P :
 RootPairing ι K M N) : P.IsIrreducib…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.isSimple_iff_of_not_isLieAbelian`：isSimple_iff_of_not_isLieAb
elian (hL : ¬ IsLieAbelian L) : IsSimpleOrder (LieIdeal R L) ↔ IsSimple R L
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A Killing Lie algebra is simple if and only if its root system is irreducible.
-/
theorem isSimple_iff_isIrreducible : (rootSystem H).IsIrreducible ↔ IsSimple K L := by
  nontriviality L
  have hL : ¬ IsLieAbelian L :=
    (isLieAbelian_iff_subsingleton K (L := L)).not.mpr (not_subsingleton L)
  rw [RootPairing.isIrreducible_iff_invtRootSubmodule, ← isSimple_iff_of_not_isLieAbelian K L hL,
    (lieIdealOrderIso H).isSimpleOrder_iff]

end LieAlgebra.IsKilling

namespace LieAlgebra

open LieModule

variable {K L : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-
**LieAlgebra.instIsIrreducibleRootSystem_of_isSimple** 是 Mathlib 中的一个实例，位于命名空间 `
LieAlgebra`。
形式化陈述：instIsIrreducibleRootSystem_of_isSimple [IsSimple K L] : (IsKilling.rootSy
stem H).IsIrreducible
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieAlgebra.HasTrivialRadical.instIsKilling`：∀ (R : Type u_1) (L : Type u
_2) [inst : CommRing R] [CharZero R] [IsDomain R] [inst_3 : LieRing L]   [inst_4
 : LieAlgebra R L] [IsNoetherian…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LieAlgebra.IsSimple.instHasTrivialRadical`：∀ (R : Type u_1) (L : Type u_
2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlge
bra.IsSimple R L], LieAlgebra.H…
· 使用定理 `LieAlgebra.IsKilling.isSimple_iff_isIrreducible`：isSimple_iff_isIrreduci
ble : (rootSystem H).IsIrreducible ↔ IsSimple K L
-/
instance instIsIrreducibleRootSystem_of_isSimple [IsSimple K L] :
    (IsKilling.rootSystem H).IsIrreducible :=
  LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mpr ‹_›

end LieAlgebra

