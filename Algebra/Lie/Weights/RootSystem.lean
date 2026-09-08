/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.RootSystem.Basic
public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# The root system associated with a Lie algebra

We show that the roots of a finite-dimensional splitting semisimple Lie algebra over a field of
characteristic 0 form a root system. We achieve this by studying root chains.

## Main results

- `LieAlgebra.IsKilling.apply_coroot_eq_cast`:
  If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer.

- `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`:
  The `α`-chain through `β` (`β - qα ... β ... β + rα`) are the only roots of the form `β + kα`.

- `LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul`:
  `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots.

- `LieAlgebra.IsKilling.rootSystem`: The root system of a finite-dimensional Lie algebra with
  non-degenerate Killing form over a field of characteristic zero,
  relative to a splitting Cartan subalgebra.

-/

@[expose] public section

noncomputable section

namespace LieAlgebra.IsKilling

open LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable (α β : Weight K H L)

set_option backward.privateInPublic true in
/-
**LieAlgebra.IsKilling.chainLength_aux** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsK
illing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma chainLength_aux (hα : α.IsNonZero) {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    ∃ n : ℕ, n • x = ⁅coroot α, x⁆ := by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The length of the `α`-chain through `β`. See `chainBotCoeff_add_chainTopCoeff`. -/
/-
**LieAlgebra.IsKilling.chainLength** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsKilli
ng`。
形式化陈述：chainLength (α β : Weight K H L) : Nat
参数：α β : Weight K H L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of the `α`-chain through `β`. See `chainBotCoeff_add_chainTopCoeff`.
-/
def chainLength (α β : Weight K H L) : ℕ :=
  letI := Classical.propDecidable
  if hα : α.IsZero then 0 else
    (chainLength_aux α β hα (chainTop α β).exists_ne_zero.choose_spec.1).choose
/-
**LieAlgebra.IsKilling.chainLength_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra.IsKilling`。
形式化陈述：chainLength_of_isZero (hα : α.IsZero) : chainLength α β = 0
参数：hα : α.IsZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma chainLength_of_isZero (hα : α.IsZero) : chainLength α β = 0 := dif_pos hα
/-
**LieAlgebra.IsKilling.chainLength_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.I
sKilling`。
形式化陈述：chainLength_nsmul {x} (hx : x in rootSpace H (chainTop α β)) : chainLength
 α β • x = ⁅coroot α, x⁆
参数：hx : x in rootSpace H (chainTop α β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieAlgebra.IsKilling.coroot_eq_zero_iff`：∀ {K : Type u_2} {L : Type u_3}
 [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : Fin
iteDimensional K L] {H : LieS…
· 使用引理 `LieAlgebra.IsKilling.chainLength_of_isZero`：chainLength_of_isZero (hα : 
α.IsZero) : chainLength α β = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用引理 `LieModule.Weight.exists_ne_zero`：exists_ne_zero (χ : Weight R L M) : exi
sts x in genWeightSpace M χ, x != 0
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`：finrank_rootSpace_eq_one 
(α : Weight K H L) (hα : α.IsNonZero) : finrank K (rootSpace H α) = 1
· 使用引理 `LieModule.chainTop_isNonZero`：chainTop_isNonZero (α β : Weight R L M) (h
α : α.IsNonZero) : (chainTop α β).IsNonZero
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
（共 34 条，此处仅展示前 30 条）
-/
lemma chainLength_nsmul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    chainLength α β • x = ⁅coroot α, x⁆ := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' ∈ rootSpace H (chainTop α β) ∧ x' ≠ 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : ∃ k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul, smul_comm, chainLength, dif_neg hα, (chainLength_aux α β hα h.1).choose_spec]
/-
**LieAlgebra.IsKilling.chainLength_smul** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Is
Killing`。
形式化陈述：chainLength_smul {x} (hx : x in rootSpace H (chainTop α β)) : (chainLength
 α β : K) • x = ⁅coroot α, x⁆
参数：hx : x in rootSpace H (chainTop α β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `LieAlgebra.IsKilling.chainLength_nsmul`：chainLength_nsmul {x} (hx : x in
 rootSpace H (chainTop α β)) : chainLength α β • x = ⁅coroot α, x⁆
-/
lemma chainLength_smul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    (chainLength α β : K) • x = ⁅coroot α, x⁆ := by
  rw [Nat.cast_smul_eq_nsmul, chainLength_nsmul _ _ hx]
/-
**LieAlgebra.IsKilling.apply_coroot_eq_cast'** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra.IsKilling`。
形式化陈述：apply_coroot_eq_cast' : β (coroot α) = ↑(chainLength α β - 2 * chainTopCoe
ff α β : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieAlgebra.IsKilling.coroot_eq_zero_iff`：∀ {K : Type u_2} {L : Type u_3}
 [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : Fin
iteDimensional K L] {H : LieS…
· 使用定理 `LieAlgebra.IsKilling.chainLength.eq_1`：∀ {K : Type u_1} {L : Type u_2} [
inst : Field K] [inst_1 : CharZero K] [inst_2 : LieRing L] [inst_3 : LieAlgebra 
K L]   [inst_4 : LieAlgebra…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `LieModule.chainTopCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
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
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用引理 `LieModule.Weight.exists_ne_zero`：exists_ne_zero (χ : Weight R L M) : exi
sts x in genWeightSpace M χ, x != 0
· 使用引理 `LieAlgebra.IsKilling.chainLength_smul`：chainLength_smul {x} (hx : x in r
ootSpace H (chainTop α β)) : (chainLength α β : K) • x = ⁅coroot α, x⁆
（共 52 条，此处仅展示前 30 条）
-/
lemma apply_coroot_eq_cast' :
    β (coroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : ℤ) := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero_iff_left x_ne0, sub_eq_zero, coe_chainTop', nsmul_eq_mul, Pi.natCast_def,
    Pi.add_apply, Pi.mul_apply, root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]
/-
**LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_le** 是 Mathlib 中的一个引理
，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：rootSpace_neg_nsmul_add_chainTop_of_le {n : Nat} (hn : n <= chainLength α 
β) : rootSpace H (-(n • α) + chainTop α β) != ⊥
参数：hn : n <= chainLength α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.rootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra
 R L) [inst_3 : LieRi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `LieModule.chainTop.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst
_3 : AddCommGroup M…
· 使用定理 `LieModule.chainTop_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRin
g R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : A
ddCommGroup M…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LieModule.Weight.genWeightSpace_ne_bot'`：∀ {R : Type u_2} {L : Type u_3}
 {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L]   [inst_3 : AddCommGroup M…
· 使用引理 `LieModule.Weight.exists_ne_zero`：exists_ne_zero (χ : Weight R L M) : exi
sts x in genWeightSpace M χ, x != 0
· 使用引理 `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero`：exists_isSl
2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : exists h e f
 : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f …
· 使用定理 `LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace`：lie_mem_genWeig
htSpace_of_mem_genWeightSpace {χ₁ χ₂ : H -> R} {x : L} {m : M} (hx : x in rootSp
ace H χ₁) (hm : m in genWeightSpace M χ₂) : ⁅…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.chainLength_smul`：chainLength_smul {x} (hx : x in r
ootSpace H (chainTop α β)) : (chainLength α β : K) • x = ⁅coroot α, x⁆
· 使用引理 `LieModule.genWeightSpace_add_chainTop`：genWeightSpace_add_chainTop : gen
WeightSpace M (α + chainTop α β : L -> R) = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LieAlgebra.toEnd_pow_apply_mem`：toEnd_pow_apply_mem {χ₁ χ₂ : H -> R} {x 
: L} {m : M} (hx : x in rootSpace H χ₁) (hm : m in genWeightSpace M χ₂) (n) : (t
oEnd R L M x ^ n : M…
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_ne_zero_of_eq_nat`：pow_to
End_f_ne_zero_of_eq_nat [CharZero R] [IsDomain R] [IsTorsionFree R M] {n : Nat} 
(hn : μ = n) {i} (hi : i <= n) : (ψ i) != 0
· 使用定理 `IsSl2Triple.h_eq_coroot`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing
 L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K
 L] {H : LieS…
-/
lemma rootSpace_neg_nsmul_add_chainTop_of_le {n : ℕ} (hn : n ≤ chainLength α β) :
    rootSpace H (-(n • α) + chainTop α β) ≠ ⊥ := by
  by_cases hα : α.IsZero
  · simpa only [hα.eq, smul_zero, neg_zero, chainTop_zero, zero_add, ne_eq] using! β.2
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α β : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  simp only [← smul_neg, ne_eq, LieSubmodule.eq_bot_iff, not_forall]
  exact ⟨_, toEnd_pow_apply_mem hf hx n, prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn⟩
/-
**LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_lt** 是 Mathlib 中的一个引理
，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：rootSpace_neg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : Nat} (hn : 
chainLength α β < n) : rootSpace H (-(n • α) + chainTop α β) = ⊥
参数：hα : α.IsNonZero；hn : chainLength α β < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用引理 `LieAlgebra.IsKilling.apply_coroot_eq_cast'`：apply_coroot_eq_cast' : β (c
oroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : Int)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieAlgebra.IsKilling.coroot_neg`：∀ {K : Type u_2} {L : Type u_3} [inst :
 LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimen
sional K L] {H : LieS…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
（共 70 条，此处仅展示前 30 条）
-/
lemma rootSpace_neg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : ℕ} (hn : chainLength α β < n) :
    rootSpace H (-(n • α) + chainTop α β) = ⊥ := by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H → K) = -(n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W ≤ chainLength (-α) W := by
    have := apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_comm (2 : K),
      add_sub_cancel, add_sub, Nat.cast_inj, eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add,
      sub_eq_iff_eq_add] at this
    lia
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H → K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg, ← smul_neg, neg_neg, ← Weight.coe_neg, H₂] at this
  exact this (genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα)
/-
**LieAlgebra.IsKilling.chainTopCoeff_le_chainLength** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：chainTopCoeff_le_chainLength : chainTopCoeff α β <= chainLength α β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.chainTopCoeff.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   
[inst_3 : AddCommGroup M…
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `LieModule.chainTopCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用引理 `LieModule.genWeightSpace_nsmul_add_ne_bot_of_le`：genWeightSpace_nsmul_ad
d_ne_bot_of_le {n} (hn : n <= chainTopCoeff α β) : genWeightSpace M (n • α + β :
 L -> R) != ⊥
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用引理 `LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_lt`：rootSpace_n
eg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : Nat} (hn : chainLength α β <
 n) : rootSpace H (-(n • α) + chainTop α β) = ⊥
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma chainTopCoeff_le_chainLength : chainTopCoeff α β ≤ chainLength α β := by
  by_cases hα : α.IsZero
  · simp only [hα.eq, chainTopCoeff_zero, zero_le]
  rw [← not_lt, ← Nat.succ_le_iff]
  intro e
  apply genWeightSpace_nsmul_add_ne_bot_of_le α β
    (Nat.sub_le (chainTopCoeff α β) (chainLength α β).succ)
  rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_sub e, sub_smul, sub_eq_neg_add,
    add_assoc, ← coe_chainTop, Nat.cast_smul_eq_nsmul]
  exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
/-
**LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff** 是 Mathlib 中的一个引理，位于命名空间
 `LieAlgebra.IsKilling`。
形式化陈述：chainBotCoeff_add_chainTopCoeff : chainBotCoeff α β + chainTopCoeff α β = 
chainLength α β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `LieModule.chainTopCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `LieModule.chainBotCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `LieAlgebra.IsKilling.chainLength_of_isZero`：chainLength_of_isZero (hα : 
α.IsZero) : chainLength α β = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_sub_iff_add_le`：∀ {k m n : ℕ}, k ≤ m → (n ≤ m - k ↔ n + k ≤ m)
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_le_chainLength`：chainTopCoeff_le_chai
nLength : chainTopCoeff α β <= chainLength α β
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `LieModule.chainBotCoeff.eq_1`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `LieModule.Weight.coe_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRin
g L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional 
K L] [inst_4 :…
· 使用引理 `LieModule.genWeightSpace_nsmul_add_ne_bot_of_le`：genWeightSpace_nsmul_ad
d_ne_bot_of_le {n} (hn : n <= chainTopCoeff α β) : genWeightSpace M (n • α + β :
 L -> R) != ⊥
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
（共 45 条，此处仅展示前 30 条）
-/
lemma chainBotCoeff_add_chainTopCoeff :
    chainBotCoeff α β + chainTopCoeff α β = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [hα.eq, chainTopCoeff_zero, chainBotCoeff_zero, zero_add, chainLength_of_isZero α β hα]
  apply le_antisymm
  · rw [← Nat.le_sub_iff_add_le (chainTopCoeff_le_chainLength α β),
      ← not_lt, ← Nat.succ_le_iff, chainBotCoeff, ← Weight.coe_neg]
    intro e
    apply genWeightSpace_nsmul_add_ne_bot_of_le _ _ e
    rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_succ, Nat.cast_sub (chainTopCoeff_le_chainLength α β),
      LieModule.Weight.coe_neg, smul_neg, ← neg_smul, neg_add_rev, neg_sub, sub_eq_neg_add,
      ← add_assoc, ← neg_add_rev, add_smul, add_assoc, ← coe_chainTop, neg_smul,
      ← @Nat.cast_one ℤ, ← Nat.cast_add, Nat.cast_smul_eq_nsmul]
    exact rootSpace_neg_nsmul_add_chainTop_of_lt α β hα (Nat.lt_succ_self _)
  · rw [← not_lt]
    intro e
    apply rootSpace_neg_nsmul_add_chainTop_of_le α β e
    rw [← Nat.succ_add, ← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
      ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero, neg_smul, ← smul_neg,
      Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_chainTopCoeff_add_one_nsmul_add (-α) β (Weight.IsNonZero.neg hα)
/-
**LieAlgebra.IsKilling.chainTopCoeff_add_chainBotCoeff** 是 Mathlib 中的一个引理，位于命名空间
 `LieAlgebra.IsKilling`。
形式化陈述：chainTopCoeff_add_chainBotCoeff : chainTopCoeff α β + chainBotCoeff α β = 
chainLength α β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff`：chainBotCoeff_add_
chainTopCoeff : chainBotCoeff α β + chainTopCoeff α β = chainLength α β
-/
lemma chainTopCoeff_add_chainBotCoeff :
    chainTopCoeff α β + chainBotCoeff α β = chainLength α β := by
  rw [add_comm, chainBotCoeff_add_chainTopCoeff]
/-
**LieAlgebra.IsKilling.chainBotCoeff_le_chainLength** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：chainBotCoeff_le_chainLength : chainBotCoeff α β <= chainLength α β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_add_chainBotCoeff`：chainTopCoeff_add_
chainBotCoeff : chainTopCoeff α β + chainBotCoeff α β = chainLength α β
-/
lemma chainBotCoeff_le_chainLength : chainBotCoeff α β ≤ chainLength α β :=
  (Nat.le_add_left _ _).trans_eq (chainTopCoeff_add_chainBotCoeff α β)

@[simp]
/-
**LieAlgebra.IsKilling.chainLength_neg** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsK
illing`。
形式化陈述：chainLength_neg : chainLength (-α) β = chainLength α β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff`：chainBotCoeff_add_
chainTopCoeff : chainBotCoeff α β + chainTopCoeff α β = chainLength α β
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LieModule.Weight.coe_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRin
g L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional 
K L] [inst_4 :…
· 使用定理 `LieModule.chainTopCoeff_neg`：∀ {R : Type u_1} {L : Type u_2} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3
 : AddCommGroup M…
· 使用定理 `LieModule.chainBotCoeff_neg`：∀ {R : Type u_1} {L : Type u_2} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3
 : AddCommGroup M…
-/
lemma chainLength_neg :
    chainLength (-α) β = chainLength α β := by
  rw [← chainBotCoeff_add_chainTopCoeff, ← chainBotCoeff_add_chainTopCoeff, add_comm,
    Weight.coe_neg, chainTopCoeff_neg, chainBotCoeff_neg]

@[simp]
/-
**LieAlgebra.IsKilling.chainLength_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Is
Killing`。
形式化陈述：chainLength_zero [Nontrivial L] : chainLength 0 β = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieAlgebra.instNontrivialSubtypeMemLieSubmoduleLieSubalgebraGenWeightSpa
ceOfNatForall`：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) [inst_3 : LieRi…
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.chainBotCoeff.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   
[inst_3 : AddCommGroup M…
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `LieModule.Weight.instIsZeroApply`：∀ {R : Type u_2} {L : Type u_3} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [i
nst_3 : AddCommGroup M…
· 使用定理 `LieModule.chainBotCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `LieModule.chainTopCoeff.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   
[inst_3 : AddCommGroup M…
· 使用定理 `LieModule.chainTopCoeff_zero`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chainLength_zero [Nontrivial L] : chainLength 0 β = 0 := by
  simp [← chainBotCoeff_add_chainTopCoeff]

/-- If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer. -/
/-
**LieAlgebra.IsKilling.apply_coroot_eq_cast** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebr
a.IsKilling`。
形式化陈述：apply_coroot_eq_cast : β (coroot α) = (chainBotCoeff α β - chainTopCoeff α
 β : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.apply_coroot_eq_cast'`：apply_coroot_eq_cast' : β (c
oroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : Int)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_add_chainBotCoeff`：chainTopCoeff_add_
chainBotCoeff : chainTopCoeff α β + chainBotCoeff α β = chainLength α β

--- 原说明 ---
If `β - qα ... β ... β + rα` is the `α`-chain through `β`, then
  `β (coroot α) = q - r`. In particular, it is an integer.
-/
lemma apply_coroot_eq_cast :
    β (coroot α) = (chainBotCoeff α β - chainTopCoeff α β : ℤ) := by
  rw [apply_coroot_eq_cast', ← chainTopCoeff_add_chainBotCoeff]; congr 1; lia
/-
**LieAlgebra.IsKilling.le_chainBotCoeff_of_rootSpace_ne_top** 是 Mathlib 中的一个引理，位
于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：le_chainBotCoeff_of_rootSpace_ne_top (hα : α.IsNonZero) (n : Int) (hn : ro
otSpace H (-n • α + β) != ⊥) : n <= chainBotCoeff α β
参数：hα : α.IsNonZero；n : Int；hn : rootSpace H (-n • α + β) != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_lt`：rootSpace_n
eg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : Nat} (hn : chainLength α β <
 n) : rootSpace H (-(n • α) + chainTop α β) = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff`：chainBotCoeff_add_
chainTopCoeff : chainBotCoeff α β + chainTopCoeff α β = chainLength α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_lt_add_iff_right`：∀ {k n m : ℕ}, n + k < m + k ↔ n < m
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
（共 31 条，此处仅展示前 30 条）
-/
lemma le_chainBotCoeff_of_rootSpace_ne_top
    (hα : α.IsNonZero) (n : ℤ) (hn : rootSpace H (-n • α + β) ≠ ⊥) :
    n ≤ chainBotCoeff α β := by
  contrapose! hn
  lift n to ℕ using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt, ← @Nat.add_lt_add_iff_right (chainTopCoeff α β),
    chainBotCoeff_add_chainTopCoeff] at hn
  have := rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero] at this

/-- Members of the `α`-chain through `β` are the only roots of the form `β - kα`. -/
/-
**LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 
`LieAlgebra.IsKilling`。
形式化陈述：rootSpace_zsmul_add_ne_bot_iff (hα : α.IsNonZero) (n : Int) : rootSpace H 
(n • α + β) != ⊥ ↔ n <= chainTopCoeff α β ∧ -n <= chainBotCoeff α β
参数：hα : α.IsNonZero；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.chainBotCoeff_neg`：∀ {R : Type u_1} {L : Type u_2} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3
 : AddCommGroup M…
· 使用定理 `LieModule.Weight.coe_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRin
g L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional 
K L] [inst_4 :…
· 使用引理 `LieAlgebra.IsKilling.le_chainBotCoeff_of_rootSpace_ne_top`：le_chainBotCo
eff_of_rootSpace_ne_top (hα : α.IsNonZero) (n : Int) (hn : rootSpace H (-n • α +
 β) != ⊥) : n <= chainBotCoeff α β
· 使用定理 `LieModule.Weight.IsNonZero.neg`：∀ {K : Type u_2} {L : Type u_3} [inst : 
LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimens
ional K L] [inst_4 :…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_le`：rootSpace_n
eg_nsmul_add_chainTop_of_le {n : Nat} (hn : n <= chainLength α β) : rootSpace H 
(-(n • α) + chainTop α β) != ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff`：chainBotCoeff_add_
chainTopCoeff : chainBotCoeff α β + chainTopCoeff α β = chainLength α β
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Members of the `α`-chain through `β` are the only roots of the form `β - kα`.
-/
lemma rootSpace_zsmul_add_ne_bot_iff (hα : α.IsNonZero) (n : ℤ) :
    rootSpace H (n • α + β) ≠ ⊥ ↔ n ≤ chainTopCoeff α β ∧ -n ≤ chainBotCoeff α β := by
  constructor
  · refine (fun hn ↦ ⟨?_, le_chainBotCoeff_of_rootSpace_ne_top α β hα _ (by rwa [neg_neg])⟩)
    rw [← chainBotCoeff_neg, ← Weight.coe_neg]
    apply le_chainBotCoeff_of_rootSpace_ne_top _ _ hα.neg
    rwa [neg_smul, Weight.coe_neg, smul_neg, neg_neg]
  · rintro ⟨h₁, h₂⟩
    set k := chainTopCoeff α β - n with hk; clear_value k
    lift k to ℕ using (by rw [hk, le_sub_iff_add_le, zero_add]; exact h₁)
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hk
    subst hk
    simp only [neg_sub, tsub_le_iff_right, ← Nat.cast_add, Nat.cast_le,
      chainBotCoeff_add_chainTopCoeff] at h₂
    have := rootSpace_neg_nsmul_add_chainTop_of_le α β h₂
    rwa [coe_chainTop, ← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul,
      ← add_assoc, ← add_smul, ← sub_eq_neg_add] at this
/-
**LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff_mem** 是 Mathlib 中的一个引理，位于命
名空间 `LieAlgebra.IsKilling`。
形式化陈述：rootSpace_zsmul_add_ne_bot_iff_mem (hα : α.IsNonZero) (n : Int) : rootSpac
e H (n • α + β) != ⊥ ↔ n in Finset.Icc (-chainBotCoeff α β : Int) (chainTopCoeff
 α β)
参数：hα : α.IsNonZero；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`：rootSpace_zsmul_add
_ne_bot_iff (hα : α.IsNonZero) (n : Int) : rootSpace H (n • α + β) != ⊥ ↔ n <= c
hainTopCoeff α β ∧ -n <= chainBotCoeff α …
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rootSpace_zsmul_add_ne_bot_iff_mem (hα : α.IsNonZero) (n : ℤ) :
    rootSpace H (n • α + β) ≠ ⊥ ↔ n ∈ Finset.Icc (-chainBotCoeff α β : ℤ) (chainTopCoeff α β) := by
  rw [rootSpace_zsmul_add_ne_bot_iff α β hα n, Finset.mem_Icc, and_comm, neg_le]
/-
**LieAlgebra.IsKilling.chainTopCoeff_of_eq_zsmul_add** 是 Mathlib 中的一个引理，位于命名空间 `
LieAlgebra.IsKilling`。
形式化陈述：chainTopCoeff_of_eq_zsmul_add (hα : α.IsNonZero) (β' : Weight K H L) (n : 
Int) (hβ' : (β' : H -> K) = n • α + β) : chainTopCoeff α β' = chainTopCoeff α β 
- n
参数：hα : α.IsNonZero；β' : Weight K H L；n : Int；hβ' : (β' : H -> K) = n • α + β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff`：rootSpace_zsmul_add
_ne_bot_iff (hα : α.IsNonZero) (n : Int) : rootSpace H (n • α + β) != ⊥ ↔ n <= c
hainTopCoeff α β ∧ -n <= chainBotCoeff α …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.coe_chainTop`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : Ad
dCommGroup M…
· 使用定理 `LieModule.Weight.genWeightSpace_ne_bot'`：∀ {R : Type u_2} {L : Type u_3}
 {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L]   [inst_3 : AddCommGroup M…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma chainTopCoeff_of_eq_zsmul_add
    (hα : α.IsNonZero) (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainTopCoeff α β' = chainTopCoeff α β - n := by
  apply le_antisymm
  · refine le_sub_iff_add_le.mpr ((rootSpace_zsmul_add_ne_bot_iff α β hα _).mp ?_).1
    rw [add_smul, add_assoc, ← hβ', ← coe_chainTop]
    exact (chainTop α β').2
  · refine ((rootSpace_zsmul_add_ne_bot_iff α β' hα _).mp ?_).1
    rw [hβ', ← add_assoc, ← add_smul, sub_add_cancel, ← coe_chainTop]
    exact (chainTop α β).2
/-
**LieAlgebra.IsKilling.chainBotCoeff_of_eq_zsmul_add** 是 Mathlib 中的一个引理，位于命名空间 `
LieAlgebra.IsKilling`。
形式化陈述：chainBotCoeff_of_eq_zsmul_add (hα : α.IsNonZero) (β' : Weight K H L) (n : 
Int) (hβ' : (β' : H -> K) = n • α + β) : chainBotCoeff α β' = chainBotCoeff α β 
+ n
参数：hα : α.IsNonZero；β' : Weight K H L；n : Int；hβ' : (β' : H -> K) = n • α + β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `LieModule.chainBotCoeff.eq_1`：∀ {R : Type u_1} {L : Type u_2} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_
3 : AddCommGroup M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.Weight.coe_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRin
g L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional 
K L] [inst_4 :…
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_of_eq_zsmul_add`：chainTopCoeff_of_eq_
zsmul_add (hα : α.IsNonZero) (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) 
= n • α + β) : chainTopCoeff α β' = chai…
· 使用定理 `LieModule.Weight.IsNonZero.neg`：∀ {K : Type u_2} {L : Type u_3} [inst : 
LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimens
ional K L] [inst_4 :…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
lemma chainBotCoeff_of_eq_zsmul_add
    (hα : α.IsNonZero) (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainBotCoeff α β' = chainBotCoeff α β + n := by
  have : (β' : H → K) = -n • (-α) + β := by rwa [neg_smul, smul_neg, neg_neg]
  rw [chainBotCoeff, chainBotCoeff, ← Weight.coe_neg,
    chainTopCoeff_of_eq_zsmul_add (-α) β hα.neg β' (-n) this, sub_neg_eq_add]
/-
**LieAlgebra.IsKilling.chainLength_of_eq_zsmul_add** 是 Mathlib 中的一个引理，位于命名空间 `Li
eAlgebra.IsKilling`。
形式化陈述：chainLength_of_eq_zsmul_add (β' : Weight K H L) (n : Int) (hβ' : (β' : H -
> K) = n • α + β) : chainLength α β' = chainLength α β
参数：β' : Weight K H L；n : Int；hβ' : (β' : H -> K) = n • α + β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.chainLength_of_isZero`：chainLength_of_isZero (hα : 
α.IsZero) : chainLength α β = 0
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_add_chainBotCoeff`：chainTopCoeff_add_
chainBotCoeff : chainTopCoeff α β + chainBotCoeff α β = chainLength α β
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_of_eq_zsmul_add`：chainTopCoeff_of_eq_
zsmul_add (hα : α.IsNonZero) (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) 
= n • α + β) : chainTopCoeff α β' = chai…
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_of_eq_zsmul_add`：chainBotCoeff_of_eq_
zsmul_add (hα : α.IsNonZero) (β' : Weight K H L) (n : Int) (hβ' : (β' : H -> K) 
= n • α + β) : chainBotCoeff α β' = chai…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma chainLength_of_eq_zsmul_add (β' : Weight K H L) (n : ℤ) (hβ' : (β' : H → K) = n • α + β) :
    chainLength α β' = chainLength α β := by
  by_cases hα : α.IsZero
  · rw [chainLength_of_isZero _ _ hα, chainLength_of_isZero _ _ hα]
  · apply Nat.cast_injective (R := ℤ)
    rw [← chainTopCoeff_add_chainBotCoeff, ← chainTopCoeff_add_chainBotCoeff,
      Nat.cast_add, Nat.cast_add, chainTopCoeff_of_eq_zsmul_add α β hα β' n hβ',
      chainBotCoeff_of_eq_zsmul_add α β hα β' n hβ', sub_eq_add_neg, add_add_add_comm,
      neg_add_cancel, add_zero]
/-
**LieAlgebra.IsKilling.chainTopCoeff_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `LieAl
gebra.IsKilling`。
形式化陈述：chainTopCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) : chainTopCoeff
 α (0 : Weight K H L) = 1
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `LieAlgebra.instNontrivialSubtypeMemLieSubmoduleLieSubalgebraGenWeightSpa
ceOfNatForall`：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) [inst_3 : LieRi…
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `LieModule.Weight.genWeightSpace_ne_bot'`：∀ {R : Type u_2} {L : Type u_3}
 {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L]   [inst_3 : AddCommGroup M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `LieModule.Weight.instIsZeroApply`：∀ {R : Type u_2} {L : Type u_3} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [i
nst_3 : AddCommGroup M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add`：genWeightSpace
_chainTopCoeff_add_one_nsmul_add : genWeightSpace M ((chainTopCoeff α β + 1) • α
 + β : L -> R) = ⊥
· 使用引理 `LieModule.Weight.exists_ne_zero`：exists_ne_zero (χ : Weight R L M) : exi
sts x in genWeightSpace M χ, x != 0
· 使用引理 `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero`：exists_isSl
2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : exists h e f
 : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f …
· 使用定理 `LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace`：lie_mem_genWeig
htSpace_of_mem_genWeightSpace {χ₁ χ₂ : H -> R} {x : L} {m : M} (hx : x in rootSp
ace H χ₁) (hm : m in genWeightSpace M χ₂) : ⁅…
· 使用引理 `LieAlgebra.IsKilling.chainLength_smul`：chainLength_smul {x} (hx : x in r
ootSpace H (chainTop α β)) : (chainLength α β : K) • x = ⁅coroot α, x⁆
· 使用引理 `LieModule.genWeightSpace_add_chainTop`：genWeightSpace_add_chainTop : gen
WeightSpace M (α + chainTop α β : L -> R) = ⊥
（共 63 条，此处仅展示前 30 条）
-/
lemma chainTopCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) :
    chainTopCoeff α (0 : Weight K H L) = 1 := by
  symm
  apply eq_of_le_of_not_lt
  · rw [Nat.one_le_iff_ne_zero]
    intro e
    exact α.2 (by simpa [e] using!
      genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα)
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α (0 : Weight K H L)).exists_ne_zero
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have prim : isSl2.HasPrimitiveVectorWith x (chainLength α (0 : Weight K H L) : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨x_ne0, (chainLength_smul _ _ hx).symm, by rwa [genWeightSpace_add_chainTop _ _ hα] at this⟩
  obtain ⟨k, hk⟩ : ∃ k : K, k • f =
      (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x := by
    have : (toEnd K L L f ^ (chainTopCoeff α (0 : Weight K H L) + 1)) x ∈ rootSpace H (-α) := by
      convert toEnd_pow_apply_mem hf hx (chainTopCoeff α (0 : Weight K H L) + 1)
      rw [coe_chainTop', FunLike.coe_zero, add_zero, succ_nsmul',
        add_assoc, smul_neg, neg_add_cancel, add_zero]
    simpa using! (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simpa using! isSl2.f_ne_zero)).mp
      (finrank_rootSpace_eq_one _ hα.neg) ⟨_, this⟩
  apply_fun (⁅f, ·⁆) at hk
  simp only [lie_smul, lie_self, smul_zero, prim.lie_f_pow_toEnd_f] at hk
  intro e
  refine prim.pow_toEnd_f_ne_zero_of_eq_nat rfl ?_ hk.symm
  have := (apply_coroot_eq_cast' α 0).symm
  simp only [← @Nat.cast_two ℤ, ← Nat.cast_mul, zero_apply, Int.cast_eq_zero, sub_eq_zero,
    Nat.cast_inj] at this
  rwa [this, Nat.succ_le_iff, two_mul, add_lt_add_iff_left]
/-
**LieAlgebra.IsKilling.chainBotCoeff_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `LieAl
gebra.IsKilling`。
形式化陈述：chainBotCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) : chainBotCoeff
 α (0 : Weight K H L) = 1
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_zero_right`：chainTopCoeff_zero_right 
[Nontrivial L] (hα : α.IsNonZero) : chainTopCoeff α (0 : Weight K H L) = 1
· 使用定理 `LieModule.Weight.IsNonZero.neg`：∀ {K : Type u_2} {L : Type u_3} [inst : 
LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimens
ional K L] [inst_4 :…
-/
lemma chainBotCoeff_zero_right [Nontrivial L] (hα : α.IsNonZero) :
    chainBotCoeff α (0 : Weight K H L) = 1 :=
  chainTopCoeff_zero_right (-α) hα.neg
/-
**LieAlgebra.IsKilling.chainLength_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra.IsKilling`。
形式化陈述：chainLength_zero_right [Nontrivial L] (hα : α.IsNonZero) : chainLength α 0
 = 2
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LieAlgebra.instNontrivialSubtypeMemLieSubmoduleLieSubalgebraGenWeightSpa
ceOfNatForall`：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) [inst_3 : LieRi…
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff`：chainBotCoeff_add_
chainTopCoeff : chainBotCoeff α β + chainTopCoeff α β = chainLength α β
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_zero_right`：chainTopCoeff_zero_right 
[Nontrivial L] (hα : α.IsNonZero) : chainTopCoeff α (0 : Weight K H L) = 1
· 使用引理 `LieAlgebra.IsKilling.chainBotCoeff_zero_right`：chainBotCoeff_zero_right 
[Nontrivial L] (hα : α.IsNonZero) : chainBotCoeff α (0 : Weight K H L) = 1
-/
lemma chainLength_zero_right [Nontrivial L] (hα : α.IsNonZero) : chainLength α 0 = 2 := by
  rw [← chainBotCoeff_add_chainTopCoeff, chainTopCoeff_zero_right α hα,
    chainBotCoeff_zero_right α hα]
/-
**LieAlgebra.IsKilling.rootSpace_two_smul** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.
IsKilling`。
形式化陈述：rootSpace_two_smul (hα : α.IsNonZero) : rootSpace H (2 • α) = ⊥
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `LieModule.Weight.instIsEmptyOfSubsingleton`：∀ {R : Type u_2} {L : Type u
_3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra
 R L]   [inst_3 : AddCommGroup M…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.rootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra
 R L) [inst_3 : LieRi…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用定理 `LieAlgebra.instNontrivialSubtypeMemLieSubmoduleLieSubalgebraGenWeightSpa
ceOfNatForall`：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) [inst_3 : LieRi…
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LieAlgebra.IsKilling.chainTopCoeff_zero_right`：chainTopCoeff_zero_right 
[Nontrivial L] (hα : α.IsNonZero) : chainTopCoeff α (0 : Weight K H L) = 1
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `LieModule.Weight.instIsZeroApply`：∀ {R : Type u_2} {L : Type u_3} {M : T
ype u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [i
nst_3 : AddCommGroup M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `LieModule.genWeightSpace_chainTopCoeff_add_one_nsmul_add`：genWeightSpace
_chainTopCoeff_add_one_nsmul_add : genWeightSpace M ((chainTopCoeff α β + 1) • α
 + β : L -> R) = ⊥
-/
lemma rootSpace_two_smul (hα : α.IsNonZero) : rootSpace H (2 • α) = ⊥ := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  simpa [chainTopCoeff_zero_right α hα] using
    genWeightSpace_chainTopCoeff_add_one_nsmul_add α (0 : Weight K H L) hα
/-
**LieAlgebra.IsKilling.rootSpace_one_div_two_smul** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Algebra.IsKilling`。
形式化陈述：rootSpace_one_div_two_smul (hα : α.IsNonZero) : rootSpace H ((2⁻¹ : K) • α
) = ⊥
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用引理 `LieAlgebra.IsKilling.rootSpace_two_smul`：rootSpace_two_smul (hα : α.IsNo
nZero) : rootSpace H (2 • α) = ⊥
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma rootSpace_one_div_two_smul (hα : α.IsNonZero) : rootSpace H ((2⁻¹ : K) • α) = ⊥ := by
  by_contra h
  let W : Weight K H L := ⟨_, h⟩
  have hW : 2 • (W : H → K) = α := by
    change 2 • (2⁻¹ : K) • (α : H → K) = α
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul]; simp
  apply α.genWeightSpace_ne_bot
  have := rootSpace_two_smul W (fun (e : (W : H → K) = 0) ↦ hα <| by
    apply_fun (2 • ·) at e; simpa [hW] using e)
  rwa [hW] at this
/-
**LieAlgebra.IsKilling.eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul** 是 Mathlib 中的
一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul (hα : α.IsNonZero) (k : K) (h :
 (β : H -> K) = k • α) : k = -1 ∨ k = 0 ∨ k = 1
参数：hα : α.IsNonZero；k : K；h : (β : H -> K) = k • α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `LieModule.Weight.instIsEmptyOfSubsingleton`：∀ {R : Type u_2} {L : Type u
_3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra
 R L]   [inst_3 : AddCommGroup M…
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
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
· 使用引理 `LieAlgebra.IsKilling.apply_coroot_eq_cast'`：apply_coroot_eq_cast' : β (c
oroot α) = ↑(chainLength α β - 2 * chainTopCoeff α β : Int)
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `LieAlgebra.instNontrivialSubtypeMemLieSubmoduleLieSubalgebraGenWeightSpa
ceOfNatForall`：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) [inst_3 : LieRi…
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff_mem`：rootSpace_zsmul
_add_ne_bot_iff_mem (hα : α.IsNonZero) (n : Int) : rootSpace H (n • α + β) != ⊥ 
↔ n in Finset.Icc (-chainBotCoeff α β : Int) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
（共 73 条，此处仅展示前 30 条）
-/
lemma eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul
    (hα : α.IsNonZero) (k : K) (h : (β : H → K) = k • α) :
    k = -1 ∨ k = 0 ∨ k = 1 := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (chainLength α β).even_or_odd with (⟨n, hn⟩ | ⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast, ← Int.cast_natCast (chainTopCoeff α β), ← Int.cast_sub] at H
    have := (rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [← Int.cast_smul_eq_zsmul K, ← H, ← h, FunLike.coe_zero, add_zero]; exact β.2)
    rw [chainTopCoeff_zero_right α hα, chainBotCoeff_zero_right α hα, Nat.cast_one] at this
    set k' : ℤ := n - chainTopCoeff α β
    subst H
    have : k' ∈ ({-1, 0, 1} : Finset ℤ) := by
      change k' ∈ Finset.Icc (-1 : ℤ) (1 : ℤ)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn, smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add, chainBotCoeff_add_chainTopCoeff, hn]
      lia
    rw [h, hk, ← Int.cast_smul_eq_zsmul K, ← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (rootSpace_one_div_two_smul α hα)

/-- `±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots. -/
/-
**LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `LieAlg
ebra.IsKilling`。
形式化陈述：eq_neg_or_eq_of_eq_smul (hβ : β.IsNonZero) (k : K) (h : (β : H -> K) = k •
 α) : β = -α ∨ β = α
参数：hβ : β.IsNonZero；k : K；h : (β : H -> K) = k • α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `LieAlgebra.IsKilling.eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul`：eq_neg_
one_or_eq_zero_or_eq_one_of_eq_smul (hα : α.IsNonZero) (k : K) (h : (β : H -> K)
 = k • α) : k = -1 ∨ k = 0 ∨ k = 1
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
`±α` are the only `K`-multiples of a root `α` that are also (non-zero) roots.
-/
lemma eq_neg_or_eq_of_eq_smul (hβ : β.IsNonZero) (k : K) (h : (β : H → K) = k • α) :
    β = -α ∨ β = α := by
  by_cases hα : α.IsZero
  · rw [hα, smul_zero] at h; cases hβ h
  rcases eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul α β hα k h with (rfl | rfl | rfl)
  · exact .inl (by ext; rw [h, neg_one_smul]; rfl)
  · cases hβ (by rwa [zero_smul] at h)
  · exact .inr (by ext; rw [h, one_smul])

/-- The reflection of a root along another. -/
/-
**LieAlgebra.IsKilling.reflectRoot** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsKilli
ng`。
形式化陈述：reflectRoot (α β : Weight K H L) : Weight K H L where toFun
参数：α β : Weight K H L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reflection of a root along another.
-/
def reflectRoot (α β : Weight K H L) : Weight K H L where
  toFun := β - β (coroot α) • α
  genWeightSpace_ne_bot' := by
    by_cases hα : α.IsZero
    · simpa [hα.eq] using β.genWeightSpace_ne_bot
    rw [sub_eq_neg_add, apply_coroot_eq_cast α β, ← neg_smul, ← Int.cast_neg,
      Int.cast_smul_eq_zsmul, rootSpace_zsmul_add_ne_bot_iff α β hα]
    lia
/-
**LieAlgebra.IsKilling.reflectRoot_isNonZero** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra.IsKilling`。
形式化陈述：reflectRoot_isNonZero (α β : Weight K H L) (hβ : β.IsNonZero) : (reflectRo
ot α β).IsNonZero
参数：α β : Weight K H L；hβ : β.IsNonZero。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieAlgebra.IsKilling.coroot_eq_zero_iff`：∀ {K : Type u_2} {L : Type u_3}
 [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : Fin
iteDimensional K L] {H : LieS…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
（共 33 条，此处仅展示前 30 条）
-/
lemma reflectRoot_isNonZero (α β : Weight K H L) (hβ : β.IsNonZero) :
    (reflectRoot α β).IsNonZero := by
  intro e
  have : β (coroot α) = 0 := by
    by_cases hα : α.IsZero
    · simp [coroot_eq_zero_iff.mpr hα]
    simpa [root_apply_coroot hα, mul_two] using congr_fun (sub_eq_zero.mp e) (coroot α)
  have : reflectRoot α β = β := by ext; simp [reflectRoot, this]
  exact hβ (this ▸ e)

variable (H)

/-- The root system of a finite-dimensional Lie algebra with non-degenerate Killing form over a
field of characteristic zero, relative to a splitting Cartan subalgebra. -/
/-
**LieAlgebra.IsKilling.rootSystem** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsKillin
g`。
形式化陈述：rootSystem : RootPairing H.root K (Dual K H) H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The root system of a finite-dimensional Lie algebra with non-degenerate Killing 
form over a
field of characteristic zero, relative to a splitting Cartan subalgebra.
-/
def rootSystem :
    RootPairing H.root K (Dual K H) H :=
  RootPairing.mk''
    .id
    { toFun := (↑)
      inj' := by
        intro α β h; ext x; simpa using LinearMap.congr_fun h x }
    { toFun := coroot ∘ (↑)
      inj' := by rintro ⟨α, hα⟩ ⟨β, hβ⟩ h; simpa using h }
    (fun ⟨α, hα⟩ ↦ by simpa using root_apply_coroot <| by simpa using hα)
    (by
      rintro ⟨α, hα⟩ - ⟨⟨β, hβ⟩, rfl⟩
      simpa using
        ⟨reflectRoot α β, by simpa using reflectRoot_isNonZero α β <| by simpa using hβ, rfl⟩)
    (by convert! span_weight_isNonZero_eq_top K L H; ext; simp)
/-
**LieAlgebra.IsKilling.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (rootSystem H).IsRootSystem :=
  RootPairing.isRootSystem_mk'' fun α β ↦
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩

@[simp]
/-
**LieAlgebra.IsKilling.corootForm_rootSystem_eq_killing** 是 Mathlib 中的一个引理，位于命名空
间 `LieAlgebra.IsKilling`。
形式化陈述：corootForm_rootSystem_eq_killing : (rootSystem H).CorootForm = (killingFor
m K L).restrict H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.restrict_killingForm_eq_sum`：restrict_killingForm_e
q_sum : (killingForm K L).restrict H = ∑ α in H.root, (α : H ->ₗ[K] K).smulRight
 (α : H ->ₗ[K] K)
· 使用定理 `RootPairing.CorootForm.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
-/
lemma corootForm_rootSystem_eq_killing :
    (rootSystem H).CorootForm = (killingForm K L).restrict H := by
  rw [restrict_killingForm_eq_sum, RootPairing.CorootForm, ← Finset.sum_coe_sort (s := H.root)]
  rfl
/-
**LieAlgebra.IsKilling.rootSystem_toLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [in
st_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieAlgebra.IsKilling K L
] [inst_5 : FiniteDimensional K L] (H : LieSubalgebra K L)   [inst_6 : H.IsCarta
nSubalgebra] [inst_7 : LieModule.IsTriangularizable K (↥H) L] (f : Module.Dual K
 ↥H) (x : ↥H),   ((LieAlgebra.IsKilling.rootSystem H).toLinearMap f) x = f x
参数：H : LieSubalgebra K L；↥H；f : Module.Dual K ↥H；x : ↥H；(LieAlgebra.IsKilling.ro
otSystem H).toLinearMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
-/
@[simp] lemma rootSystem_toLinearMap_apply (f x) : (rootSystem H).toLinearMap f x = f x := rfl
/-
**LieAlgebra.IsKilling.rootSystem_pairing_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAl
gebra.IsKilling`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [in
st_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieAlgebra.IsKilling K L
] [inst_5 : FiniteDimensional K L] (H : LieSubalgebra K L)   [inst_6 : H.IsCarta
nSubalgebra] [inst_7 : LieModule.IsTriangularizable K (↥H) L] (α β : ↥LieSubalge
bra.root),   (LieAlgebra.IsKilling.rootSystem H).pairing β α = ↑β (LieAlgebra.Is
Killing.coroot ↑α)
参数：H : LieSubalgebra K L；↥H；α β : ↥LieSubalgebra.root；LieAlgebra.IsKilling.rootS
ystem H；LieAlgebra.IsKilling.coroot ↑α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma rootSystem_pairing_apply (α β) : (rootSystem H).pairing β α = β.1 (coroot α.1) := rfl
/-
**LieAlgebra.IsKilling.rootSystem_root_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgeb
ra.IsKilling`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [in
st_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieAlgebra.IsKilling K L
] [inst_5 : FiniteDimensional K L] (H : LieSubalgebra K L)   [inst_6 : H.IsCarta
nSubalgebra] [inst_7 : LieModule.IsTriangularizable K (↥H) L] (α : ↥LieSubalgebr
a.root),   (LieAlgebra.IsKilling.rootSystem H).root α = LieModule.Weight.toLinea
r K (↥H) L ↑α
参数：H : LieSubalgebra K L；↥H；α : ↥LieSubalgebra.root；LieAlgebra.IsKilling.rootSys
tem H；↥H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma rootSystem_root_apply (α) : (rootSystem H).root α = α := rfl
/-
**LieAlgebra.IsKilling.rootSystem_coroot_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlg
ebra.IsKilling`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : CharZero K] [in
st_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieAlgebra.IsKilling K L
] [inst_5 : FiniteDimensional K L] (H : LieSubalgebra K L)   [inst_6 : H.IsCarta
nSubalgebra] [inst_7 : LieModule.IsTriangularizable K (↥H) L] (α : ↥LieSubalgebr
a.root),   (LieAlgebra.IsKilling.rootSystem H).coroot α = LieAlgebra.IsKilling.c
oroot ↑α
参数：H : LieSubalgebra K L；↥H；α : ↥LieSubalgebra.root；LieAlgebra.IsKilling.rootSys
tem H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma rootSystem_coroot_apply (α) : (rootSystem H).coroot α = coroot α := rfl

open LieSubmodule in
@[simp]
/-
**LieAlgebra.IsKilling.biSup_corootSpace_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `LieAl
gebra.IsKilling`。
形式化陈述：biSup_corootSpace_eq_top : ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), coroot
Space α = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton`：coe_corootSpace_
eq_span_singleton (α : Weight K H L) : (corootSpace α).toSubmodule = K ∙ coroot 
α
· 使用定理 `Submodule.iSup_span`：iSup_span {ι : Sort*} (p : ι -> Set M) : ⨆ i, span 
R (p i) = span R (⋃ i, p i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.IsRootSystem.span_coroot_eq_top`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `LieAlgebra.IsKilling.instIsRootSystemSubtypeWeightMemLieSubalgebraFinset
RootDualRootSystem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : C
harZero K] [inst_2 : LieRing L] [inst_3 : LieAlgebra K L]   [inst_4 : LieAlgebra
…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma biSup_corootSpace_eq_top :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤ := by
  simp only [← toSubmodule_inj, top_toSubmodule, iSup_toSubmodule,
    ← RootPairing.IsRootSystem.span_coroot_eq_top (P := rootSystem H),
    coe_corootSpace_eq_span_singleton, Submodule.iSup_span]
  congr
  ext α
  simp [eq_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LieAlgebra.IsKilling.biSup_corootSubmodule_eq_cartan** 是 Mathlib 中的一个引理，位于命名空间
 `LieAlgebra.IsKilling`。
形式化陈述：biSup_corootSubmodule_eq_cartan : ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
 corootSubmodule α = H.toLieSubmodule
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.biSup_corootSpace_eq_top`：biSup_corootSpace_eq_top 
: ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieModuleHom.map_top`：map_top : LieSubmodule.map f ⊤ = f.range
· 使用定理 `LieSubmodule.range_incl`：range_incl : N.incl.range = N
-/
lemma biSup_corootSubmodule_eq_cartan :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSubmodule α = H.toLieSubmodule := by
  suffices ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), corootSpace α = ⊤ from
    le_antisymm (by simp) (by simp [← LieSubmodule.map_iSup, this])
  simp
/-
**LieAlgebra.IsKilling.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (rootSystem H).IsCrystallographic where
  exists_value α β :=
    ⟨chainBotCoeff β.1 α.1 - chainTopCoeff β.1 α.1, by simp [apply_coroot_eq_cast β.1 α.1]⟩
/-
**LieAlgebra.IsKilling.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (rootSystem H).IsReduced where
  eq_or_eq_neg := by
    intro ⟨α, hα⟩ ⟨β, hβ⟩ e
    rw [LinearIndependent.pair_iff' ((rootSystem H).ne_zero _), not_forall] at e
    simp only [rootSystem_root_apply, ne_eq, not_not] at e
    obtain ⟨u, hu⟩ := e
    obtain (h | h) := eq_neg_or_eq_of_eq_smul α β (by simpa using hβ) u
      (by ext x; exact DFunLike.congr_fun hu.symm x)
    · right; ext x; simpa [neg_eq_iff_eq_neg] using DFunLike.congr_fun h.symm x
    · left; ext x; simpa using DFunLike.congr_fun h.symm x

end LieAlgebra.IsKilling

