/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!

# The root system base associated to a Lie algebra basis

-/

@[expose] public section

noncomputable section

namespace LieAlgebra.Basis

open AddSubmonoid Function IsKilling LieModule LieSubalgebra Matrix Set

variable {ι K L : Type*} [Fintype ι] [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} (b : Basis ι H)

/-- The elements `LieAlgebra.Basis.baseSupp` as roots in the sense of `LieSubalgebra.root`. -/
/-
**LieAlgebra.Basis.baseSupp'** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：baseSupp' (i : ι) : letI
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The elements `LieAlgebra.Basis.baseSupp` as roots in the sense of `LieSubalgebra
.root`.
-/
def baseSupp' (i : ι) :
    letI := b.isCartanSubalgebra
    H.root := by
  let := b.isCartanSubalgebra
  refine ⟨⟨b.baseSupp i, ?_⟩, ?_⟩
  · simp only [LieSubmodule.eq_bot_iff, ne_eq, not_forall]
    exact ⟨b.e i, (mem_genWeightSpace _ _ _).mpr fun x ↦ ⟨1, by simp⟩, (b.sl2 i).e_ne_zero⟩
  · simpa [Weight.IsNonZero, Weight.IsZero] using b.linearIndependent_baseSupp.ne_zero i
/-
**LieAlgebra.Basis.coe_linearMap_baseSupp'** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra
.Basis`。
形式化陈述：∀ {ι : Type u_1} {K : Type u_2} {L : Type u_3} [inst : Fintype ι] [inst_1 
: Field K] [inst_2 : CharZero K]   [inst_3 : LieRing L] [inst_4 : LieAlgebra K L
] [inst_5 : FiniteDimensional K L] {H : LieSubalgebra K L}   (b : LieAlgebra.Bas
is ι H) (i : ι), LieModule.Weight.toLinear K (↥H) L ↑(b.baseSupp' i) = b.baseSup
p i
参数：b : LieAlgebra.Basis ι H；i : ι；↥H；b.baseSupp' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.Basis.isCartanSubalgebra`：isCartanSubalgebra [IsNoetherian R 
L] : H.IsCartanSubalgebra
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
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
-/
@[simp] lemma coe_linearMap_baseSupp' (i : ι) : b.baseSupp' i = b.baseSupp i := rfl

variable [IsTriangularizable K H L] [IsKilling K L]
/-
**LieAlgebra.Basis.linearIndepOn_root_baseSupp** 是 Mathlib 中的一个引理，位于命名空间 `LieAlg
ebra.Basis`。
形式化陈述：linearIndepOn_root_baseSupp : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.Basis.isCartanSubalgebra`：isCartanSubalgebra [IsNoetherian R 
L] : H.IsCartanSubalgebra
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `LieAlgebra.Basis.linearIndependent_baseSupp`：linearIndependent_baseSupp 
[IsDomain R] [CharZero R] : LinearIndependent R b.baseSupp
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `LieModule.Weight.mk.injEq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4
} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 :
 AddCommGroup M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
lemma linearIndepOn_root_baseSupp :
    letI := b.isCartanSubalgebra
    LinearIndepOn K (rootSystem H).root (range b.baseSupp') := by
  let e : ι ≃ range b.baseSupp' := Equiv.ofInjective _ <| fun i j hij ↦
    b.linearIndependent_baseSupp.injective <| by simpa [baseSupp'] using hij
  rw [LinearIndepOn, ← linearIndependent_equiv e]
  exact b.linearIndependent_baseSupp
/-
**LieAlgebra.Basis.root_mem_or_mem_neg** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Bas
is`。
形式化陈述：root_mem_or_mem_neg (χ : letI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.Basis.isCartanSubalgebra`：isCartanSubalgebra [IsNoetherian R 
L] : H.IsCartanSubalgebra
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.sum_smul_mem`：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι 
-> R) (hyp : forall c in t, f c in p) : (∑ i in t, r i • f i) in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LieAlgebra.Basis.iSup_cartan_borelLower_borelUpper_eq_top`：iSup_cartan_b
orelLower_borelUpper_eq_top : iSup ![H.toLieSubmodule, b.borelLower, b.borelUppe
r] = ⊤
· 使用定理 `iSup_union`：iSup_union {f : β -> α} {s t : Set β} : ⨆ x in s union t, f 
x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
（共 52 条，此处仅展示前 30 条）
-/
lemma root_mem_or_mem_neg (χ : letI := b.isCartanSubalgebra; H.root) :
    letI := b.isCartanSubalgebra
    ( (rootSystem H).root χ ∈ closure ((rootSystem H).root '' range b.baseSupp') ∨
     -(rootSystem H).root χ ∈ closure ((rootSystem H).root '' range b.baseSupp')) := by
  let := b.isCartanSubalgebra
  have (n : ι → ℕ) :
      ∑ i, n i • b.baseSupp i ∈ closure (⇑(rootSystem H).root '' range b.baseSupp') := by
    simp_rw [← Submodule.span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid]
    exact Submodule.sum_smul_mem _ _ fun i _ ↦ Submodule.subset_span <| by simp
  let s : Set (H → K) := {0} ∪
    {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = -∑ i, n i • b.baseSupp i} ∪
    {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f =  ∑ i, n i • b.baseSupp i}
  have hs : ⨆ α ∈ s, rootSpace H α = ⊤ := by
    have := b.iSup_cartan_borelLower_borelUpper_eq_top
    rw [borelLower_eq, borelUpper_eq, b.cartan_eq] at this
    rw [iSup_union, iSup_union]
    simpa [iSup_and, iSup_comm (ι := H → K)] using this
  obtain ⟨χ, hχ⟩ := χ
  change χ.toLinear ∈ _ ∨ -χ.toLinear ∈ _
  replace hs : ⇑χ ∈ s :=
    (iSupIndep_genWeightSpace K H L).mem_of_biSup_eq_top hs χ.genWeightSpace_ne_bot
  replace hs : (∃ n : ι → ℕ, n ≠ 0 ∧ χ.toLinear = -∑ i, n i • b.baseSupp i) ∨
               (∃ n : ι → ℕ, n ≠ 0 ∧ χ.toLinear = ∑ i, n i • b.baseSupp i) := by
    have hχ' : ¬ χ.IsZero := by simpa using hχ
    simp only [hχ', s, singleton_union, mem_union, mem_insert_iff, Weight.coe_eq_zero_iff,
      mem_ofPred_eq, false_or] at hs
    simpa only [← LinearMap.coe_neg, ← Weight.coe_coe, LinearMap.coe_injective.eq_iff] using hs
  refine hs.symm.imp (fun ⟨n, hn₀, hn⟩ ↦ ?_) (fun ⟨n, hn₀, hn⟩ ↦ ?_) <;> simpa [hn] using this n

/-- The distinguished root system base associated to a basis. -/
/-
**LieAlgebra.Basis.base** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：base : letI
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `LieAlgebra.Basis.linearIndepOn_root_baseSupp`：linearIndepOn_root_baseSup
p : letI
· 使用引理 `LieAlgebra.Basis.root_mem_or_mem_neg`：root_mem_or_mem_neg (χ : letI

--- 原说明 ---
The distinguished root system base associated to a basis.
-/
def base :
    letI := b.isCartanSubalgebra
    RootPairing.Base (rootSystem H) :=
  letI := b.isCartanSubalgebra
  .mk' (rootSystem H) (range b.baseSupp') b.linearIndepOn_root_baseSupp b.root_mem_or_mem_neg

/-- The support of `LieAlgebra.Basis.base` is in one-to-one correspondence with the indexing
set of the basis. -/
/-
**LieAlgebra.Basis.baseSupportEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`
。
形式化陈述：baseSupportEquiv : ι ≃ b.base.support
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The support of `LieAlgebra.Basis.base` is in one-to-one correspondence with the 
indexing
set of the basis.
-/
def baseSupportEquiv : ι ≃ b.base.support :=
  have : Injective b.baseSupp' :=
    fun i j hij ↦ b.linearIndependent_baseSupp.injective <| by simpa [baseSupp'] using hij
  (Equiv.ofInjective _ this).trans (Set.Finite.subtypeEquivToFinset _)
/-
**LieAlgebra.Basis.coe_baseSupportEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlge
bra.Basis`。
形式化陈述：∀ {ι : Type u_1} {K : Type u_2} {L : Type u_3} [inst : Fintype ι] [inst_1 
: Field K] [inst_2 : CharZero K]   [inst_3 : LieRing L] [inst_4 : LieAlgebra K L
] [inst_5 : FiniteDimensional K L] {H : LieSubalgebra K L}   (b : LieAlgebra.Bas
is ι H) [inst_6 : LieModule.IsTriangularizable K (↥H) L] [inst_7 : LieAlgebra.Is
Killing K L]   (i : ι), LieModule.Weight.toLinear K (↥H) L ↑↑(b.baseSupportEquiv
 i) = b.baseSupp i
参数：b : LieAlgebra.Basis ι H；↥H；i : ι；↥H；b.baseSupportEquiv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.Basis.isCartanSubalgebra`：isCartanSubalgebra [IsNoetherian R 
L] : H.IsCartanSubalgebra
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma coe_baseSupportEquiv_apply (i : ι) : b.baseSupportEquiv i = b.baseSupp i := rfl
/-
**LieAlgebra.Basis.coroot_eq_h'** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：∀ {ι : Type u_1} {K : Type u_2} {L : Type u_3} [inst : Fintype ι] [inst_1 
: Field K] [inst_2 : CharZero K]   [inst_3 : LieRing L] [inst_4 : LieAlgebra K L
] [inst_5 : FiniteDimensional K L] {H : LieSubalgebra K L}   (b : LieAlgebra.Bas
is ι H) [inst_6 : LieModule.IsTriangularizable K (↥H) L] [inst_7 : LieAlgebra.Is
Killing K L]   (i : ι), LieAlgebra.IsKilling.coroot ↑↑(b.baseSupportEquiv i) = b
.h' i
参数：b : LieAlgebra.Basis ι H；↥H；i : ι；b.baseSupportEquiv i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `LieAlgebra.Basis.isCartanSubalgebra`：isCartanSubalgebra [IsNoetherian R 
L] : H.IsCartanSubalgebra
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
· 使用定理 `LieAlgebra.Basis.sl2`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [in
st : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra
 R L] {H :…
· 使用定理 `LieAlgebra.Basis.cartan_eq_lieSpan`：∀ {ι : Type u_1} {R : Type u_2} {L :
 Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_
3 : LieAlgebra R L] {H :…
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieModule.mem_genWeightSpace`：mem_genWeightSpace (χ : L -> R) (m : M) : 
m in genWeightSpace M χ ↔ forall x, exists k : Nat, ((toEnd R L M x - χ x • ↑1) 
^ k) m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieAlgebra.Basis.baseSupp_apply_smul_e`：∀ {ι : Type u_1} {R : Type u_2} 
{L : Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [i
nst_3 : LieAlgebra R L] {H :…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
（共 43 条，此处仅展示前 30 条）
-/
@[simp] lemma coroot_eq_h' (i : ι) :
    letI := b.isCartanSubalgebra
    coroot (b.baseSupportEquiv i) = b.h' i := by
  let := b.isCartanSubalgebra
  suffices b.h' i ∈ corootSpace (b.baseSupp' i) by
    have _i : IsAddTorsionFree L := .of_isTorsionFree K L
    exact (eq_coroot_of_mem_corootSpace_of_two (b.baseSupp' i).val this (by simp [baseSupp'])).symm
  have h_mem : ⁅b.e i, b.f i⁆ ∈ H := by
    nth_rw 1 [(b.sl2 i).lie_e_f, b.cartan_eq_lieSpan]
    exact subset_lieSpan <| mem_range_self i
  have h_eq : b.h' i = ⟨⁅b.e i, b.f i⁆, h_mem⟩ := by simp [(b.sl2 i).lie_e_f, h']
  rw [h_eq]
  have he : b.e i ∈ rootSpace H (b.baseSupp i) :=
    (mem_genWeightSpace _ _ _).mpr fun ⟨z, hz⟩ ↦ ⟨1, by simp⟩
  have hf : b.f i ∈ rootSpace H (-b.baseSupp i) :=
    (mem_genWeightSpace _ _ _).mpr fun ⟨z, hz⟩ ↦ ⟨1, by simp [← eq_neg_iff_add_eq_zero]⟩
  exact (mem_corootSpace _).mpr <| Submodule.subset_span ⟨b.e i, he, b.f i, hf, rfl⟩
/-
**LieAlgebra.Basis.cartanMatrix_base_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Ba
sis`。
形式化陈述：cartanMatrix_base_eq : b.base.cartanMatrix = b.A.reindex b.baseSupportEqui
v b.baseSupportEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.Basis.isCartanSubalgebra`：isCartanSubalgebra [IsNoetherian R 
L] : H.IsCartanSubalgebra
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LieAlgebra.IsKilling.instIsCrystallographicSubtypeWeightMemLieSubalgebra
FinsetRootDualRootSystem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst
_1 : CharZero K] [inst_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieA
lgebra…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.reindex_apply`：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matri
x m n α) : reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)
· 使用引理 `RootPairing.Base.algebraMap_cartanMatrixIn_apply`：algebraMap_cartanMatri
xIn_apply (i j : b.support) : algebraMap S R (b.cartanMatrixIn S i j) = P.pairin
g i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieAlgebra.Basis.coroot_eq_h'`：∀ {ι : Type u_1} {K : Type u_2} {L : Type
 u_3} [inst : Fintype ι] [inst_1 : Field K] [inst_2 : CharZero K]   [inst_3 : Li
eRing L] [inst_4 : …
· 使用定理 `LieAlgebra.Basis.baseSupp_apply_h'`：∀ {ι : Type u_1} {R : Type u_2} {L :
 Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_
3 : LieAlgebra R L] {H :…
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
lemma cartanMatrix_base_eq :
    b.base.cartanMatrix = b.A.reindex b.baseSupportEquiv b.baseSupportEquiv := by
  suffices b.base.cartanMatrix.reindex b.baseSupportEquiv.symm b.baseSupportEquiv.symm = b.A by
    rwa [← (reindex b.baseSupportEquiv b.baseSupportEquiv).symm_apply_eq]
  ext i j
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [reindex_apply, submatrix_apply, RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  simp [← Weight.coe_coe]

end LieAlgebra.Basis

