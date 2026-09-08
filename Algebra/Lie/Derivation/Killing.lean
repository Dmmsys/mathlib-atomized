/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Derivations of finite-dimensional Killing Lie algebras

This file establishes that all derivations of finite-dimensional Killing Lie algebras are inner.

## Main statements

- `LieDerivation.Killing.ad_mem_orthogonal_of_mem_orthogonal`: if a derivation `D` is in the Killing
  orthogonal of the range of the adjoint action, then, for any `x : L`, `ad (D x)` is also in this
  orthogonal.
- `LieDerivation.Killing.range_ad_eq_top`: in a finite-dimensional Lie algebra with non-degenerate
  Killing form, the range of the adjoint action is full,
- `LieDerivation.Killing.exists_eq_ad`: in a finite-dimensional Lie algebra with non-degenerate
  Killing form, any derivation is an inner derivation.
-/

@[expose] public section

namespace LieDerivation.IsKilling

section

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

/-- A local notation for the set of (Lie) derivations on `L`. -/
local notation "𝔻" => (LieDerivation R L L)

/-- A local notation for the range of `ad`. -/
local notation "𝕀" => (LieHom.range (ad R L))

/-- A local notation for the Killing complement of the ideal range of `ad`. -/
local notation "𝕀ᗮ" => LinearMap.BilinForm.orthogonal (killingForm R 𝔻) 𝕀

/-
**LieDerivation.IsKilling.killingForm_restrict_range_ad** 是 Mathlib 中的一个引理，位于命名空
间 `LieDerivation.IsKilling`。
形式化陈述：killingForm_restrict_range_ad [Module.Finite R L] : (killingForm R 𝔻).rest
rict 𝕀 = killingForm R 𝕀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.IsIdealMorphism.eq`：∀ {R : Type u} {L : Type v} {L' : Type w₂} [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieRing L']   [inst_3 : LieAlge
bra R L'] [inst…
· 使用引理 `LieDerivation.ad_isIdealMorphism`：ad_isIdealMorphism : (ad R L).IsIdealM
orphism
· 使用引理 `LieIdeal.killingForm_eq`：killingForm_eq : killingForm R I = (killingForm
 R L).restrict I
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
lemma killingForm_restrict_range_ad [Module.Finite R L] :
    (killingForm R 𝔻).restrict 𝕀 = killingForm R 𝕀 := by
  rw [← (ad_isIdealMorphism R L).eq, ← LieIdeal.killingForm_eq]
  rfl

/-- The orthogonal complement of the inner derivations is a Lie submodule of all derivations. -/
/-
**LieDerivation.IsKilling.rangeAdOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `LieDeriva
tion.IsKilling`。
形式化陈述：(R : Type u_1) →   (L : Type u_2) →     [inst : Field R] → [inst_1 : LieRi
ng L] → [inst_2 : LieAlgebra R L] → LieSubmodule R L (LieDerivation R L L)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal complement of the inner derivations is a Lie submodule of all der
ivations.
-/
@[simps!] noncomputable def rangeAdOrthogonal : LieSubmodule R L (LieDerivation R L L) where
  __ := 𝕀ᗮ
  lie_mem := by
    intro x D hD
    have : 𝕀ᗮ = (ad R L).idealRange.killingCompl := by simp [← (ad_isIdealMorphism R L).eq]
    change D ∈ 𝕀ᗮ at hD
    change ⁅x, D⁆ ∈ 𝕀ᗮ
    rw [this] at hD ⊢
    rw [← lie_ad]
    exact lie_mem_right _ _ (ad R L).idealRange.killingCompl _ _ hD

variable {R L}

/-- If a derivation `D` is in the Killing orthogonal of the range of the adjoint action, then, for
any `x : L`, `ad (D x)` is also in this orthogonal. -/
/-
**LieDerivation.IsKilling.ad_mem_orthogonal_of_mem_orthogonal** 是 Mathlib 中的一个引理
，位于命名空间 `LieDerivation.IsKilling`。
形式化陈述：ad_mem_orthogonal_of_mem_orthogonal {D : LieDerivation R L L} (hD : D in 𝕀
ᗮ) (x : L) : ad R L (D x) in 𝕀ᗮ
参数：hD : D in 𝕀ᗮ；x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […

--- 原说明 ---
If a derivation `D` is in the Killing orthogonal of the range of the adjoint act
ion, then, for
any `x : L`, `ad (D x)` is also in this orthogonal.
-/
lemma ad_mem_orthogonal_of_mem_orthogonal {D : LieDerivation R L L} (hD : D ∈ 𝕀ᗮ) (x : L) :
    ad R L (D x) ∈ 𝕀ᗮ := by
  simp only [ad_apply_lieDerivation, LieHom.range_toSubmodule, neg_mem_iff]
  exact (rangeAdOrthogonal R L).lie_mem hD

variable [Module.Finite R L]
/-
**LieDerivation.IsKilling.ad_mem_ker_killingForm_ad_range_of_mem_orthogonal** 是 
Mathlib 中的一个引理，位于命名空间 `LieDerivation.IsKilling`。
形式化陈述：ad_mem_ker_killingForm_ad_range_of_mem_orthogonal {D : LieDerivation R L L
} (hD : D in 𝕀ᗮ) (x : L) : ad R L (D x) in (LinearMap.ker (killingForm R 𝕀)).map
 (LieHom.range (ad R L)).subtype
参数：hD : D in 𝕀ᗮ；x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieDerivation.IsKilling.killingForm_restrict_range_ad`：killingForm_restr
ict_range_ad [Module.Finite R L] : (killingForm R 𝔻).restrict 𝕀 = killingForm R 
𝕀
· 使用引理 `LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict`：inf_orthogonal_
self_le_ker_restrict {W : Submodule R M} (b₁ : B.IsRefl) : W ⊓ B.orthogonal W <=
 (LinearMap.ker <| B.restrict W).map W.subtyp…
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `LieModule.traceForm_isSymm`：traceForm_isSymm : LinearMap.IsSymm (traceFo
rm R L M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LieDerivation.IsKilling.ad_mem_orthogonal_of_mem_orthogonal`：ad_mem_orth
ogonal_of_mem_orthogonal {D : LieDerivation R L L} (hD : D in 𝕀ᗮ) (x : L) : ad R
 L (D x) in 𝕀ᗮ
-/
lemma ad_mem_ker_killingForm_ad_range_of_mem_orthogonal
    {D : LieDerivation R L L} (hD : D ∈ 𝕀ᗮ) (x : L) :
    ad R L (D x) ∈ (LinearMap.ker (killingForm R 𝕀)).map (LieHom.range (ad R L)).subtype := by
  rw [← killingForm_restrict_range_ad]
  exact LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl ⟨by simp, ad_mem_orthogonal_of_mem_orthogonal hD x⟩

variable (R L)
variable [LieAlgebra.IsKilling R L]
/-
**LieDerivation.IsKilling.ad_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieDer
ivation.IsKilling`。
形式化陈述：∀ (R : Type u_1) (L : Type u_2) [inst : Field R] [inst_1 : LieRing L] [ins
t_2 : LieAlgebra R L] [Module.Finite R L]   [LieAlgebra.IsKilling R L] (x : L), 
(LieDerivation.ad R L) x = 0 ↔ x = 0
参数：R : Type u_1；L : Type u_2；x : L；LieDerivation.ad R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `LieAlgebra.center_eq_bot`：center_eq_bot [LieModule.IsFaithful R L L] : c
enter R L = ⊥
· 使用定理 `LieAlgebra.instIsFaithfulOfHasTrivialRadical`：∀ (R : Type u_1) (L : Type
 u_2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieA
lgebra.HasTrivialRadical R L], Lie…
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
· 使用引理 `LieDerivation.ad_ker_eq_center`：ad_ker_eq_center : (ad R L).ker = LieAlg
ebra.center R L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ad_apply_eq_zero_iff (x : L) : ad R L x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rwa [← LieHom.mem_ker, ad_ker_eq_center, LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at h
/-
**LieDerivation.IsKilling.instIsKilling_range_ad** 是 Mathlib 中的一个实例，位于命名空间 `LieD
erivation.IsKilling`。
形式化陈述：instIsKilling_range_ad : LieAlgebra.IsKilling R 𝕀
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieEquiv.isKilling`：∀ {R : Type u_1} {L : Type u_3} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {L' : Type u_4}   [inst_3 : LieRi
ng L'] […
· 使用引理 `LieDerivation.injective_ad_of_center_eq_bot`：injective_ad_of_center_eq_b
ot (h : LieAlgebra.center R L = ⊥) : Function.Injective (ad R L)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.center_eq_bot`：center_eq_bot [LieModule.IsFaithful R L L] : c
enter R L = ⊥
· 使用定理 `LieAlgebra.instIsFaithfulOfHasTrivialRadical`：∀ (R : Type u_1) (L : Type
 u_2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieA
lgebra.HasTrivialRadical R L], Lie…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsKilling_range_ad : LieAlgebra.IsKilling R 𝕀 :=
  (LieEquiv.ofInjective (ad R L) (injective_ad_of_center_eq_bot <| by simp)).isKilling

/-- The restriction of the Killing form of a finite-dimensional Killing Lie algebra to the range of
the adjoint action is nondegenerate. -/
/-
**LieDerivation.IsKilling.killingForm_restrict_range_ad_nondegenerate** 是 Mathli
b 中的一个引理，位于命名空间 `LieDerivation.IsKilling`。
形式化陈述：killingForm_restrict_range_ad_nondegenerate : ((killingForm R 𝔻).restrict 
𝕀).Nondegenerate
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `LieDerivation.IsKilling.killingForm_restrict_range_ad`：killingForm_restr
ict_range_ad [Module.Finite R L] : (killingForm R 𝔻).restrict 𝕀 = killingForm R 
𝕀
· 使用引理 `LieAlgebra.IsKilling.killingForm_nondegenerate`：killingForm_nondegenerat
e : (killingForm R L).Nondegenerate

--- 原说明 ---
The restriction of the Killing form of a finite-dimensional Killing Lie algebra 
to the range of
the adjoint action is nondegenerate.
-/
lemma killingForm_restrict_range_ad_nondegenerate :
    ((killingForm R 𝔻).restrict 𝕀).Nondegenerate := by
  convert! LieAlgebra.IsKilling.killingForm_nondegenerate R 𝕀
  exact killingForm_restrict_range_ad R L

set_option backward.isDefEq.respectTransparency false in
/-- The range of the adjoint action on a finite-dimensional Killing Lie algebra is full. -/
@[simp]
/-
**LieDerivation.IsKilling.range_ad_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivati
on.IsKilling`。
形式化陈述：range_ad_eq_top : 𝕀 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用引理 `LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bo
t`：eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot (b₁ : B.IsRefl) (b₂ : (
B.restrict W).Nondegenerate) (b₃ : B.orthogonal W = ⊥) : W = ⊤
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `LieModule.traceForm_isSymm`：traceForm_isSymm : LinearMap.IsSymm (traceFo
rm R L M)
· 使用引理 `LieDerivation.IsKilling.killingForm_restrict_range_ad_nondegenerate`：kil
lingForm_restrict_range_ad_nondegenerate : ((killingForm R 𝔻).restrict 𝕀).Nondeg
enerate
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用引理 `LieDerivation.IsKilling.ad_mem_ker_killingForm_ad_range_of_mem_orthogona
l`：ad_mem_ker_killingForm_ad_range_of_mem_orthogonal {D : LieDerivation R L L} (
hD : D in 𝕀ᗮ) (x : L) : ad R L (D x) in (LinearMap.ker (killing…

--- 原说明 ---
The range of the adjoint action on a finite-dimensional Killing Lie algebra is f
ull.
-/
lemma range_ad_eq_top : 𝕀 = ⊤ := by
  rw [← LieSubalgebra.toSubmodule_inj]
  apply LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl (killingForm_restrict_range_ad_nondegenerate R L)
  refine (Submodule.eq_bot_iff _).mpr fun D hD ↦ ext fun x ↦ ?_
  simpa using ad_mem_ker_killingForm_ad_range_of_mem_orthogonal hD x

variable {R L} in
/-- Every derivation of a finite-dimensional Killing Lie algebra is an inner derivation. -/
/-
**LieDerivation.IsKilling.exists_eq_ad** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation.
IsKilling`。
形式化陈述：exists_eq_ad (D : 𝔻) : exists x, ad R L x = D
参数：D : 𝔻。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieDerivation.IsKilling.range_ad_eq_top`：range_ad_eq_top : 𝕀 = ⊤
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤

--- 原说明 ---
Every derivation of a finite-dimensional Killing Lie algebra is an inner derivat
ion.
-/
lemma exists_eq_ad (D : 𝔻) : ∃ x, ad R L x = D := by
  change D ∈ 𝕀
  rw [range_ad_eq_top R L]
  exact Submodule.mem_top

end

end IsKilling

end LieDerivation

