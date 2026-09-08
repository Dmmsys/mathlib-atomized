/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Weights.Chain
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Roots of Lie algebras with non-degenerate Killing forms

The file contains definitions and results about roots of Lie algebras with non-degenerate Killing
forms.

## Main definitions
* `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`: if the Killing form of
  a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
* `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`: if the Killing form of a Lie
  algebra is non-singular, then its Cartan subalgebras are Abelian.
* `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`: over a perfect field, if a Lie
  algebra has non-degenerate Killing form, Cartan subalgebras contain only semisimple elements.
* `LieAlgebra.IsKilling.span_weight_eq_top`: given a splitting Cartan subalgebra `H` of a
  finite-dimensional Lie algebra with non-singular Killing form, the corresponding roots span the
  dual space of `H`.
* `LieAlgebra.IsKilling.coroot`: the coroot corresponding to a root.
* `LieAlgebra.IsKilling.isCompl_ker_weight_span_coroot`: given a root `α` with respect to a Cartan
  subalgebra `H`, we have a natural decomposition of `H` as the kernel of `α` and the span of the
  coroot corresponding to `α`.
* `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`: root spaces are one-dimensional.
* `LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`: a Lie ideal decomposes as its
  intersection with the Cartan subalgebra plus a sum of root spaces.

-/

@[expose] public section

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

/-
**LieAlgebra.restrict_killingForm** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：restrict_killingForm (H : LieSubalgebra R L) : (killingForm R L).restrict 
H = LieModule.traceForm R H L
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_killingForm (H : LieSubalgebra R L) :
    (killingForm R L).restrict H = LieModule.traceForm R H L :=
  rfl

namespace IsKilling

variable [IsKilling R L]

/-- If the Killing form of a Lie algebra is non-singular, it remains non-singular when restricted
to a Cartan subalgebra. -/
/-
**LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra** 是 Mathlib 中的一
个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：ker_restrict_eq_bot_of_isCartanSubalgebra [IsNoetherian R L] [IsArtinian R
 L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] : LinearMap.ker ((killingForm
 R L).restrict H) = ⊥
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用引理 `LieModule.isCompl_genWeightSpace_zero_posFittingComp`：isCompl_genWeightS
pace_zero_posFittingComp : IsCompl (genWeightSpace M 0) (posFittingComp R L M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `LieSubalgebra.coe_toLieSubmodule`：coe_toLieSubmodule : (K.toLieSubmodule
 : Submodule R L) = K
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `LieSubmodule.sup_toSubmodule`：sup_toSubmodule : (↑(N ⊔ N') : Submodule R
 M) = (N : Submodule R M) ⊔ (N' : Submodule R M)
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用引理 `killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting`：killingForm_eq_zero_
of_mem_zeroRoot_mem_posFitting (H : LieSubalgebra R L) [LieRing.IsNilpotent H] {
x₀ x₁ : L} (hx₀ : x₀ in LieAlgebra.zeroR…
· 使用定理 `LieAlgebra.le_zeroRootSubalgebra`：le_zeroRootSubalgebra : H <= zeroRootS
ubalgebra R L H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LinearMap.BilinForm.ker_restrict_eq_of_codisjoint`：ker_restrict_eq_of_co
disjoint {p q : Submodule R M} (hpq : Codisjoint p q) {B : LinearMap.BilinForm R
 M} (hB : forall x in p, forall y in q,…
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the Killing form of a Lie algebra is non-singular, it remains non-singular wh
en restricted
to a Cartan subalgebra.
-/
lemma ker_restrict_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker ((killingForm R L).restrict H) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmodule_inj, LieSubmodule.sup_toSubmodule,
      LieSubmodule.top_toSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁
/-
**LieAlgebra.IsKilling.ker_traceForm_eq_bot_of_isCartanSubalgebra** 是 Mathlib 中的
一个定理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：∀ (R : Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L]   [LieAlgebra.IsKilling R L] [IsNoetherian R L] [IsArti
nian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra],   LinearMap.ker (LieMo
dule.traceForm R (↥H) L) = ⊥
参数：R : Type u_1；L : Type u_3；H : LieSubalgebra R L；LieModule.traceForm R (↥H) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`：ker_rest
rict_eq_bot_of_isCartanSubalgebra [IsNoetherian R L] [IsArtinian R L] (H : LieSu
balgebra R L) [H.IsCartanSubalgebra] : LinearMap.ker…
-/
@[simp] lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (LieModule.traceForm R H L) = ⊥ :=
  ker_restrict_eq_bot_of_isCartanSubalgebra R L H
/-
**LieAlgebra.IsKilling.traceForm_cartan_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 
`LieAlgebra.IsKilling`。
形式化陈述：traceForm_cartan_nondegenerate [IsNoetherian R L] [IsArtinian R L] (H : Li
eSubalgebra R L) [H.IsCartanSubalgebra] : (LieModule.traceForm R H L).Nondegener
ate
参数：H : LieSubalgebra R L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用引理 `LieModule.traceForm_isSymm`：traceForm_isSymm : LinearMap.IsSymm (traceFo
rm R L M)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.IsKilling.ker_traceForm_eq_bot_of_isCartanSubalgebra`：∀ (R : 
Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieA
lgebra R L]   [LieAlgebra.IsKilling R L] [IsNoetheria…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma traceForm_cartan_nondegenerate
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieModule.traceForm R H L).Nondegenerate := by
  simp [LinearMap.separatingLeft_iff_ker_eq_bot,
    (LieModule.traceForm_isSymm R H L).isRefl.nondegenerate_iff_separatingLeft]

variable [Module.Free R L] [Module.Finite R L]
/-
**LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra** 是 Mathlib 中的一个实例，位
于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：instIsLieAbelianOfIsCartanSubalgebra [IsDomain R] [IsPrincipalIdealRing R]
 [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] : IsLieAbelian 
H
参数：H : LieSubalgebra R L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.isLieAbelian_of_ker_traceForm_eq_bot`：isLieAbelian_of_ker_trac
eForm_eq_bot [Module.Free R M] [Module.Finite R M] (h : LinearMap.ker (traceForm
 R L M) = ⊥) : IsLieAbelian L
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`：ker_rest
rict_eq_bot_of_isCartanSubalgebra [IsNoetherian R L] [IsArtinian R L] (H : LieSu
balgebra R L) [H.IsCartanSubalgebra] : LinearMap.ker…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
-/
instance instIsLieAbelianOfIsCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    IsLieAbelian H :=
  LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L <|
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

end IsKilling

section Field

open Module LieModule Set
open Submodule (span subset_span)

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

section
variable [IsTriangularizable K H L]

/-- For any `α` and `β`, the corresponding root spaces are orthogonal with respect to the Killing
form, provided `α + β ≠ 0`. -/
/-
**LieAlgebra.killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero** 是 Mathl
ib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H -> K} {
x y : L} (hx : x in rootSpace H α) (hy : y in rootSpace H β) (hαβ : α + β != 0) 
: killingForm K L x y = 0
参数：hx : x in rootSpace H α；hy : y in rootSpace H β；hαβ : α + β != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_ne_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b ≠ b ↔ a ≠ 0
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `LieAlgebra.mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace`：mapsTo_toEn
d_genWeightSpace_add_of_mem_rootSpace (α χ : H -> R) {x : L} (hx : x in rootSpac
e H α) : MapsTo (toEnd R L M x) (genWeightSpace M…
· 使用定理 `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`：isInternal_s
ubmodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} (hi : iSupIndep A)
 (hs : iSup A = ⊤) : IsInternal A
· 使用定理 `LieSubmodule.iSupIndep_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Typ
e w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] […
· 使用引理 `LieModule.iSupIndep_genWeightSpace`：iSupIndep_genWeightSpace : iSupIndep
 fun χ : L -> R => genWeightSpace M χ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LieSubmodule.iSup_toSubmodule_eq_top`：∀ {R : Type u} {L : Type v} {M : T
ype w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [ins
t_3 : _root_.Module R M] […
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top`：iSup_genWeightSpace_eq_top [IsTria
ngularizable K L M] : ⨆ χ : L -> K, genWeightSpace M χ = ⊤
· 使用引理 `LinearMap.trace_eq_zero_of_mapsTo_ne`：trace_eq_zero_of_mapsTo_ne (h : Is
Internal N) [IsNoetherian R M] (σ : ι -> ι) (hσ : forall i, σ i != i) {f : Modul
e.End R M} (hf : forall i,…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …

--- 原说明 ---
For any `α` and `β`, the corresponding root spaces are orthogonal with respect t
o the Killing
form, provided `α + β ≠ 0`.
-/
lemma killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H → K} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hαβ : α + β ≠ 0) :
    killingForm K L x y = 0 := by
  /- If `ad R L z` is semisimple for all `z ∈ H` then writing `⟪x, y⟫ = killingForm K L x y`, there
  is a slick proof of this lemma that requires only invariance of the Killing form as follows.
  For any `z ∈ H`, we have:
  `α z • ⟪x, y⟫ = ⟪α z • x, y⟫ = ⟪⁅z, x⁆, y⟫ = - ⟪x, ⁅z, y⁆⟫ = - ⟪x, β z • y⟫ = - β z • ⟪x, y⟫`.
  Since this is true for any `z`, we thus have: `(α + β) • ⟪x, y⟫ = 0`, and hence the result.
  However the semisimplicity of `ad R L z` is (a) non-trivial and (b) requires the assumption
  that `K` is a perfect field and `L` has non-degenerate Killing form. -/
  let σ : (H → K) → (H → K) := fun γ ↦ α + (β + γ)
  have hσ : ∀ γ, σ γ ≠ γ := fun γ ↦ by simpa only [σ, ← add_assoc] using add_ne_right.mpr hαβ
  let f : Module.End K L := (ad K L x) ∘ₗ (ad K L y)
  have hf : ∀ γ, MapsTo f (rootSpace H γ) (rootSpace H (σ γ)) := fun γ ↦
    (mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α (β + γ) hx).comp <|
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L β γ hy
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace K H L)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top K H L)
  exact LinearMap.trace_eq_zero_of_mapsTo_ne hds σ hσ hf

/-- Elements of the `α` root space which are Killing-orthogonal to the `-α` root space are
Killing-orthogonal to all of `L`. -/
/-
**LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg** 是 Ma
thlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg {α : H -> K} 
{x : L} (hx : x in rootSpace H α) (hx' : forall y in rootSpace H (-α), killingFo
rm K L x y = 0) : x in LinearMap.ker (killingForm K L)
参数：hx : x in rootSpace H α；hx' : forall y in rootSpace H (-α), killingForm K L x
 y = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top`：iSup_genWeightSpace_eq_top [IsTria
ngularizable K L M] : ⨆ χ : L -> K, genWeightSpace M χ = ⊤
· 使用定理 `LieSubmodule.iSup_induction'`：iSup_induction' {ι} (N : ι -> LieSubmodule
 R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop} (mem : forall (i) (x) (hx 
: x in N i), motiv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用引理 `LieAlgebra.killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero`：ki
llingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H -> K} {x y : L}
 (hx : x in rootSpace H α) (hy : y in rootSpace H β) (hαβ …
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Elements of the `α` root space which are Killing-orthogonal to the `-α` root spa
ce are
Killing-orthogonal to all of `L`.
-/
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hx' : ∀ y ∈ rootSpace H (-α), killingForm K L x y = 0) :
    x ∈ LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y ∈ ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | mem β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  | zero => simp
  | add => simp_all
end

end Field

end LieAlgebra

namespace LieModule

namespace Weight

open LieAlgebra IsKilling

variable {K L}

variable [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L] {α : Weight K H L}

/-
**LieModule.Weight.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Weight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveNeg (Weight K H L) where
  neg α := ⟨-α, by
    by_cases hα : α.IsZero
    · convert! α.genWeightSpace_ne_bot; rw [hα, neg_zero]
    · intro e
      obtain ⟨x, hx, x_ne0⟩ := α.exists_ne_zero
      have := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hx
        (fun y hy ↦ by rw [rootSpace, e] at hy; rw [hy, map_zero])
      rw [ker_killingForm_eq_bot] at this
      exact x_ne0 this⟩
  neg_neg α := by ext; simp
/-
**LieModule.Weight.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] [inst_4 : LieAlgebra.Is
Killing K L] {H : LieSubalgebra K L}   [inst_5 : H.IsCartanSubalgebra] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] {α : LieModule.Weight K (↥H) L},   ⇑(-α)
 = -⇑α
参数：↥H；↥H；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
-/
@[simp] lemma coe_neg : ((-α : Weight K H L) : H → K) = -α := rfl
/-
**LieModule.Weight.IsZero.neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight.IsZero
`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] [inst_4 : LieAlgebra.Is
Killing K L] {H : LieSubalgebra K L}   [inst_5 : H.IsCartanSubalgebra] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] {α : LieModule.Weight K (↥H) L},   α.IsZ
ero → (-α).IsZero
参数：↥H；↥H；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.Weight.coe_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRin
g L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional 
K L] [inst_4 :…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma IsZero.neg (h : α.IsZero) : (-α).IsZero := by ext; rw [coe_neg, h, neg_zero]
/-
**LieModule.Weight.isZero_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] [inst_4 : LieAlgebra.Is
Killing K L] {H : LieSubalgebra K L}   [inst_5 : H.IsCartanSubalgebra] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] {α : LieModule.Weight K (↥H) L},   (-α).
IsZero ↔ α.IsZero
参数：↥H；↥H；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LieModule.Weight.IsZero.neg`：∀ {K : Type u_2} {L : Type u_3} [inst : Lie
Ring L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimension
al K L] [inst_4 :…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma isZero_neg : (-α).IsZero ↔ α.IsZero := ⟨fun h ↦ neg_neg α ▸ h.neg, fun h ↦ h.neg⟩
/-
**LieModule.Weight.IsNonZero.neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight.IsN
onZero`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] [inst_4 : LieAlgebra.Is
Killing K L] {H : LieSubalgebra K L}   [inst_5 : H.IsCartanSubalgebra] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] {α : LieModule.Weight K (↥H) L},   α.IsN
onZero → (-α).IsNonZero
参数：↥H；↥H；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `LieModule.Weight.IsZero.neg`：∀ {K : Type u_2} {L : Type u_3} [inst : Lie
Ring L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimension
al K L] [inst_4 :…
-/
lemma IsNonZero.neg (h : α.IsNonZero) : (-α).IsNonZero := fun e ↦ h (by simpa using e.neg)
/-
**LieModule.Weight.isNonZero_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] [inst_4 : LieAlgebra.Is
Killing K L] {H : LieSubalgebra K L}   [inst_5 : H.IsCartanSubalgebra] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] {α : LieModule.Weight K (↥H) L},   (-α).
IsNonZero ↔ α.IsNonZero
参数：↥H；↥H；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `LieModule.Weight.isZero_neg`：∀ {K : Type u_2} {L : Type u_3} [inst : Lie
Ring L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimension
al K L] [inst_4 :…
-/
@[simp] lemma isNonZero_neg {α : Weight K H L} : (-α).IsNonZero ↔ α.IsNonZero := isZero_neg.not
/-
**LieModule.Weight.toLinear_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModule.Weight`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] [inst_4 : LieAlgebra.Is
Killing K L] {H : LieSubalgebra K L}   [inst_5 : H.IsCartanSubalgebra] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] {α : LieModule.Weight K (↥H) L},   LieMo
dule.Weight.toLinear K (↥H) L (-α) = -LieModule.Weight.toLinear K (↥H) L α
参数：↥H；↥H；↥H；-α；↥H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
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
-/
@[simp] lemma toLinear_neg {α : Weight K H L} : (-α).toLinear = -α.toLinear := rfl

end Weight

end LieModule

namespace LieAlgebra

open Module LieModule Set
open Submodule renaming span → span
open Submodule renaming subset_span → subset_span

namespace IsKilling

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
variable [IsKilling K L]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- If a Lie algebra `L` has non-degenerate Killing form, the only element of a Cartan subalgebra
whose adjoint action on `L` is nilpotent, is the zero element.

Over a perfect field a much stronger result is true, see
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`. -/
/-
**LieAlgebra.IsKilling.eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra** 是 M
athlib 中的一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x in H) 
(hx' : _root_.IsNilpotent (ad K L x)) : x = 0
参数：hx : x in H；hx' : _root_.IsNilpotent (ad K L x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_lie_eq`：commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
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
· 使用引理 `LieModule.traceForm_apply_apply`：traceForm_apply_apply (x y : L) : trace
Form R L M x y = trace R _ (φ x ∘ₗ φ y)
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `LinearMap.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpo
tent {f : M ->ₗ[R] M} (hf : IsNilpotent f) : IsNilpotent (trace R M f)
· 使用定理 `Commute.isNilpotent_mul_right`：isNilpotent_mul_right (h_comm : Commute x
 y) (h : IsNilpotent x) : IsNilpotent (x * y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubmonoid.mk_eq_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] (S : A
ddSubmonoid M) {a : M} {ha : a ∈ S}, ⟨a, ha⟩ = 0 ↔ a = 0
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If a Lie algebra `L` has non-degenerate Killing form, the only element of a Cart
an subalgebra
whose adjoint action on `L` is nilpotent, is the zero element.

Over a perfect field a much stronger result is true, see
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`.
-/
lemma eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H)
    (hx' : _root_.IsNilpotent (ad K L x)) : x = 0 := by
  suffices ⟨x, hx⟩ ∈ LinearMap.ker (traceForm K H L) by
    simp only [ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.mem_bot] at this
    exact (AddSubmonoid.mk_eq_zero H.toAddSubmonoid).mp this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K H L y) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, map_zero]
  rw [traceForm_apply_apply, ← Module.End.mul_eq_comp, LinearMap.zero_apply]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (comm.isNilpotent_mul_right hx')).eq_zero

@[simp]
/-
**LieAlgebra.IsKilling.corootSpace_zero_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieAlg
ebra.IsKilling`。
形式化陈述：corootSpace_zero_eq_bot : corootSpace (0 : H -> K) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `LieSubalgebra.zero_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L),   0 ∈ L
'
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `LieAlgebra.rootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra
 R L) [inst_3 : LieRi…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
-/
lemma corootSpace_zero_eq_bot :
    corootSpace (0 : H → K) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  suffices {x | ∃ y ∈ H, ∃ z ∈ H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z, hz⟩ : H)⁆ = 0 by
    simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using this
  simp [trivial_lie_zero]

variable {K L} in
/-- The restriction of the Killing form to a Cartan subalgebra, as a linear equivalence to the
dual. -/
@[simps! apply_apply]
/-
**LieAlgebra.IsKilling.cartanEquivDual** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsK
illing`。
形式化陈述：cartanEquivDual : H ≃ₗ[K] Module.Dual K H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of the Killing form to a Cartan subalgebra, as a linear equivale
nce to the
dual.
-/
noncomputable def cartanEquivDual :
    H ≃ₗ[K] Module.Dual K H :=
  (traceForm K H L).toDual <| traceForm_cartan_nondegenerate K L H

variable {K L H}

/-- The coroot corresponding to a root. -/
/-
**LieAlgebra.IsKilling.coroot** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：coroot (α : Weight K H L) : H
参数：α : Weight K H L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coroot corresponding to a root.
-/
noncomputable def coroot (α : Weight K H L) : H :=
  2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α
/-
**LieAlgebra.IsKilling.traceForm_coroot** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Is
Killing`。
形式化陈述：traceForm_coroot (α : Weight K H L) (x : H) : traceForm K H L (coroot α) x
 = 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • α x
参数：α : Weight K H L；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `LieAlgebra.IsKilling.coroot.eq_1`：∀ {K : Type u_2} {L : Type u_3} [inst 
: LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDime
nsional K L] {H : LieS…
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
-/
lemma traceForm_coroot (α : Weight K H L) (x : H) :
    traceForm K H L (coroot α) x = 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • α x := by
  have : cartanEquivDual H ((cartanEquivDual H).symm α) x = α x := by
    rw [LinearEquiv.apply_symm_apply, Weight.toLinear_apply]
  rw [coroot, map_nsmul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  congr 2
/-
**LieAlgebra.IsKilling.coroot_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.IsKillin
g`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] {H : LieSubalgebra K L}
 [inst_4 : H.IsCartanSubalgebra]   [inst_5 : LieAlgebra.IsKilling K L] [inst_6 :
 LieModule.IsTriangularizable K (↥H) L] (α : LieModule.Weight K (↥H) L),   LieAl
gebra.IsKilling.coroot (-α) = -LieAlgebra.IsKilling.coroot α
参数：↥H；α : LieModule.Weight K (↥H) L；-α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coroot_neg [IsTriangularizable K H L] (α : Weight K H L) :
    coroot (-α) = -coroot α := by
  simp [coroot]

variable [IsTriangularizable K H L]
/-
**LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace
_neg_aux** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux {α : Wei
ght K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace H (-α)) (a
ux : forall (h : H), ⁅h, e⁆ = α h • e) : ⁅e, f⁆ = killingForm K L e f • (cartanE
quivDual H).symm α
参数：heα : e in rootSpace H α；hfα : f in rootSpace H (-α)；aux : forall (h : H), ⁅h
, e⁆ = α h • e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用引理 `LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg`
：mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg {α : H -> K} {x : 
L} (hx : x in rootSpace H α) (hx' : forall y in rootSpace H (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieAlgebra.rootSpace_zero_eq`：rootSpace_zero_eq (H : LieSubalgebra R L) 
[H.IsCartanSubalgebra] [IsNoetherian R L] : rootSpace H 0 = H.toLieSubmodule
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.genWeightSpace.congr_simp`：∀ {R : Type u_2} {L : Type u_3} (M 
: Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]  
 [inst_3 : AddCommGroup M…
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieAlgebra.mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace`：mapsTo_toEn
d_genWeightSpace_add_of_mem_rootSpace (α χ : H -> R) {x : L} (hx : x in rootSpac
e H α) : MapsTo (toEnd R L M x) (genWeightSpace M…
· 使用定理 `LieSubalgebra.smul_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R
) {x : L}, x…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LieAlgebra.rootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra
 R L) [inst_3 : LieRi…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `LinearMap.BilinForm.apply_toDual_symm_apply`：apply_toDual_symm_apply {B 
: BilinForm K V} {hB : B.Nondegenerate} (f : Module.Dual K V) (v : V) : B ((B.to
Dual hB).symm f) v = f v
（共 43 条，此处仅展示前 30 条）
-/
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α))
    (aux : ∀ (h : H), ⁅h, e⁆ = α h • e) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by
  set α' := (cartanEquivDual H).symm α
  rw [← sub_eq_zero, ← Submodule.mem_bot (R := K), ← ker_killingForm_eq_bot]
  apply mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg (α := (0 : H → K))
  · simp only [rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule]
    refine sub_mem ?_ (H.smul_mem _ α'.property)
    simpa using mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α (-α) heα hfα
  · intro z hz
    replace hz : z ∈ H := by simpa using hz
    have he : ⁅z, e⁆ = α ⟨z, hz⟩ • e := aux ⟨z, hz⟩
    have hαz : killingForm K L α' (⟨z, hz⟩ : H) = α ⟨z, hz⟩ :=
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) _ _
    simp [traceForm_comm K L L ⁅e, f⁆, ← traceForm_apply_lie_apply, he, mul_comm _ (α ⟨z, hz⟩), hαz]

/-- This is Proposition 4.18 from [carter2005] except that we use
`LieModule.exists_forall_lie_eq_smul` instead of Lie's theorem (and so avoid
assuming `K` has characteristic zero). -/
/-
**LieAlgebra.IsKilling.cartanEquivDual_symm_apply_mem_corootSpace** 是 Mathlib 中的
一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) : (cartanEqu
ivDual H).symm α in corootSpace α
参数：α : Weight K H L。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `LieModule.exists_forall_lie_eq_smul`：exists_forall_lie_eq_smul [LinearWe
ights R L M] [IsNoetherian R M] (χ : Weight R L M) : exists m : M, m != 0 ∧ fora
ll x : L, ⁅x, m⁆ = χ x • …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieModule.mem_genWeightSpace`：mem_genWeightSpace (χ : L -> R) (m : M) : 
m in genWeightSpace M χ ↔ forall x, exists k : Nat, ((toEnd R L M x - χ x • ↑1) 
^ k) m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用引理 `LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg`
：mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg {α : H -> K} {x : 
L} (hx : x in rootSpace H α) (hx' : forall y in rootSpace H (…
· 使用引理 `LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_roo
tSpace_neg_aux`：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_au
x {α : Weight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSp…
· 使用引理 `LieAlgebra.mem_corootSpace`：mem_corootSpace {x : H} : x in corootSpace α
 ↔ (x : L) in Submodule.span R {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H 
(-α))}
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
This is Proposition 4.18 from [carter2005] except that we use
`LieModule.exists_forall_lie_eq_smul` instead of Lie's theorem (and so avoid
assuming `K` has characteristic zero).
-/
lemma cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) :
    (cartanEquivDual H).symm α ∈ corootSpace α := by
  obtain ⟨e : L, he₀ : e ≠ 0, he : ∀ x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e ∈ rootSpace H α := (mem_genWeightSpace L α e).mpr fun x ↦ ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  suffices ⁅e, f⁆ = killingForm K L e f • ((cartanEquivDual H).symm α : L) from
    (mem_corootSpace α).mpr <| Submodule.subset_span ⟨(killingForm K L e f)⁻¹ • e,
      Submodule.smul_mem _ _ heα, f, hfα, by simpa [inv_smul_eq_iff₀ hf]⟩
  exact lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα he
/-
**LieAlgebra.IsKilling.coroot_mem_corootSpace** 是 Mathlib 中的一个定理，位于命名空间 `LieAlge
bra.IsKilling`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] {H : LieSubalgebra K L}
 [inst_4 : H.IsCartanSubalgebra]   [inst_5 : LieAlgebra.IsKilling K L] [LieModul
e.IsTriangularizable K (↥H) L] (α : LieModule.Weight K (↥H) L),   LieAlgebra.IsK
illing.coroot α ∈ LieAlgebra.corootSpace ⇑α
参数：↥H；α : LieModule.Weight K (↥H) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `LieAlgebra.IsKilling.cartanEquivDual_symm_apply_mem_corootSpace`：cartanE
quivDual_symm_apply_mem_corootSpace (α : Weight K H L) : (cartanEquivDual H).sym
m α in corootSpace α
-/
@[simp] lemma coroot_mem_corootSpace (α : Weight K H L) :
    coroot α ∈ corootSpace α :=
  nsmul_mem (Submodule.smul_mem _ _ <| cartanEquivDual_symm_apply_mem_corootSpace α) _

/-- Given a splitting Cartan subalgebra `H` of a finite-dimensional Lie algebra with non-singular
Killing form, the corresponding roots span the dual space of `H`. -/
@[simp]
/-
**LieAlgebra.IsKilling.span_weight_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.
IsKilling`。
形式化陈述：span_weight_eq_top : span K (range (Weight.toLinear K H L)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
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
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.traceForm_flip`：∀ (R : Type u_1) (L : Type u_3) (M : Type u_4)
 [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : 
AddCommGroup M…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `LinearMap.dualAnnihilator_ker_eq_range_flip`：dualAnnihilator_ker_eq_rang
e_flip [IsReflexive K V₂] : (ker B).dualAnnihilator = range B.flip
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `LieAlgebra.IsKilling.ker_traceForm_eq_bot_of_isCartanSubalgebra`：∀ (R : 
Type u_1) (L : Type u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieA
lgebra R L]   [LieAlgebra.IsKilling R L] [IsNoetheria…
· 使用定理 `Submodule.dualAnnihilator_bot`：dualAnnihilator_bot : (⊥ : Submodule R M)
.dualAnnihilator = ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `LieModule.range_traceForm_le_span_weight`：range_traceForm_le_span_weight
 : LinearMap.range (traceForm K L M) <= span K (range (Weight.toLinear K L M))

--- 原说明 ---
Given a splitting Cartan subalgebra `H` of a finite-dimensional Lie algebra with
 non-singular
Killing form, the corresponding roots span the dual space of `H`.
-/
lemma span_weight_eq_top :
    span K (range (Weight.toLinear K H L)) = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L, ← LinearMap.dualAnnihilator_ker_eq_range_flip,
    ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.dualAnnihilator_bot]

variable (K L H) in
@[simp]
/-
**LieAlgebra.IsKilling.span_weight_isNonZero_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：span_weight_isNonZero_eq_top : span K ({α : Weight K H L | α.IsNonZero}.im
age (Weight.toLinear K H L)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.span_weight_eq_top`：span_weight_eq_top : span K (ra
nge (Weight.toLinear K H L)) = ⊤
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Submodule.span_insert_zero`：span_insert_zero : span R (insert (0 : M) s)
 = span R s
-/
lemma span_weight_isNonZero_eq_top :
    span K ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) = ⊤ := by
  rw [← span_weight_eq_top]
  refine le_antisymm (Submodule.span_mono <| by simp) ?_
  suffices range (Weight.toLinear K H L) ⊆
    insert 0 ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) by
    simpa only [Submodule.span_insert_zero] using Submodule.span_mono this
  rintro - ⟨α, rfl⟩
  simp only [mem_insert_iff, Weight.coe_toLinear_eq_zero_iff, mem_image, mem_ofPred_eq]
  tauto

@[simp]
/-
**LieAlgebra.IsKilling.iInf_ker_weight_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra.IsKilling`。
形式化陈述：iInf_ker_weight_eq_bot : ⨅ α : Weight K H L, α.ker = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
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
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subspace.dualAnnihilator_inj`：dualAnnihilator_inj {W W' : Subspace K V} 
: W.dualAnnihilator = W'.dualAnnihilator ↔ W = W'
· 使用定理 `Subspace.dualAnnihilator_iInf_eq`：dualAnnihilator_iInf_eq {ι : Type*} [F
inite ι] (W : ι -> Subspace K V₁) : (⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W
 i).dualAnnihilator
· 使用定理 `LieModule.Weight.instFinite`：∀ (R : Type u_2) (L : Type u_3) (M : Type u
_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3
 : AddCommGroup M…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `Submodule.dualAnnihilator_bot`：dualAnnihilator_bot : (⊥ : Submodule R M)
.dualAnnihilator = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LinearMap.range_dualMap_dual_eq_span_singleton`：LinearMap.range_dualMap_
dual_eq_span_singleton (f : Dual R M₁) : range f.dualMap = R ∙ f
· 使用引理 `LieAlgebra.IsKilling.span_weight_eq_top`：span_weight_eq_top : span K (ra
nge (Weight.toLinear K H L)) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iInf_ker_weight_eq_bot :
    ⨅ α : Weight K H L, α.ker = ⊥ := by
  rw [← Subspace.dualAnnihilator_inj, Subspace.dualAnnihilator_iInf_eq,
    Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

section PerfectField

variable [PerfectField K]

open Module.End in
/-
**LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra** 是 Mathlib 中的一
个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：isSemisimple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x in H) : (ad K L 
x).IsSemisimple
参数：hx : x in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.exists_isNilpotent_isSemisimple`：exists_isNilpotent_isSemisim
ple [PerfectField K] : existsᵉ (n in adjoin K {f}) (s in adjoin K {f}), IsNilpot
ent n ∧ IsSemisimple s ∧ f = n +…
· 使用引理 `Algebra.commute_of_mem_adjoin_self`：commute_of_mem_adjoin_self {a b : A}
 (hb : b in R[a]) : Commute a b
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieModule.genWeightSpace_le_genWeightSpaceOf`：genWeightSpace_le_genWeigh
tSpaceOf (x : L) (χ : L -> R) : genWeightSpace M χ <= genWeightSpaceOf M (χ x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil`：app
ly_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil {μ : R} {k : Nat∞} {m : M}
 (hm : m in f.genEigenspace μ k) (hfg : Commute f g) (hss…
· 使用定理 `Module.End.maxGenEigenspace_eq`：maxGenEigenspace_eq [IsNoetherian R M] (
f : End R M) (μ : R) : maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspac
eIndex f μ)
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.End.IsSemisimple.isFinitelySemisimple`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   {f : Module.End R M}, f.IsSemis…
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace`：mapsTo_toEn
d_genWeightSpace_add_of_mem_rootSpace (α χ : H -> R) {x : L} (hx : x in rootSpac
e H α) : MapsTo (toEnd R L M x) (genWeightSpace M…
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieModule.iSup_genWeightSpace_eq_top`：iSup_genWeightSpace_eq_top [IsTria
ngularizable K L M] : ⨆ χ : L -> K, genWeightSpace M χ = ⊤
· 使用定理 `LieSubmodule.iSup_induction'`：iSup_induction' {ι} (N : ι -> LieSubmodule
 R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop} (mem : forall (i) (x) (hx 
: x in N i), motiv…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 55 条，此处仅展示前 30 条）
-/
lemma isSemisimple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H) :
    (ad K L x).IsSemisimple := by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_of_add_eq hSN.symm] at hN
  /- Note that the semisimple part `S` is just a scalar action on each root space. -/
  have aux {α : H → K} {y : L} (hy : y ∈ rootSpace H α) : S y = α x' • y := by
    replace hy : y ∈ (ad K L x).maxGenEigenspace (α x') :=
      (genWeightSpace_le_genWeightSpaceOf L x' α) hy
    rw [maxGenEigenspace_eq] at hy
    set k := maxGenEigenspaceIndex (ad K L x) (α x')
    rw [apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hy hS₀ hS.isFinitelySemisimple hN]
  /- So `S` obeys the derivation axiom if we restrict to root spaces. -/
  have h_der (y z : L) (α β : H → K) (hy : y ∈ rootSpace H α) (hz : z ∈ rootSpace H β) :
      S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hyz : ⁅y, z⁆ ∈ rootSpace H (α + β) :=
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β hy hz
    rw [aux hy, aux hz, aux hyz, smul_lie, lie_smul, ← add_smul, ← Pi.add_apply]
  /- Thus `S` is a derivation since root spaces span. -/
  replace h_der (y z : L) : S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hy : y ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    have hz : z ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      induction hz using LieSubmodule.iSup_induction' with
      | mem β z hz => exact h_der y z α β hy hz
      | zero => simp
      | add _ _ _ _ h h' => simp only [lie_add, map_add, h, h']; abel
    | zero => simp
    | add _ _ _ _ h h' => simp only [add_lie, map_add, h, h']; abel
  /- An equivalent form of the derivation axiom used in `LieDerivation`. -/
  replace h_der : ∀ y z : L, S ⁅y, z⁆ = ⁅y, S z⁆ - ⁅z, S y⁆ := by
    simp_rw [← lie_skew (S _) _, add_comm, ← sub_eq_add_neg] at h_der; assumption
  /- Bundle `S` as a `LieDerivation`. -/
  let S' : LieDerivation K L L := ⟨S, h_der⟩
  /- Since `L` has non-degenerate Killing form, `S` must be inner, corresponding to some `y : L`. -/
  obtain ⟨y, hy⟩ := LieDerivation.IsKilling.exists_eq_ad S'
  /- `y` commutes with all elements of `H` because `S` has eigenvalue 0 on `H`, `S = ad K L y`. -/
  have hy' (z : L) (hz : z ∈ H) : ⁅y, z⁆ = 0 := by
    rw [← LieSubalgebra.mem_toLieSubmodule, ← rootSpace_zero_eq] at hz
    simp [S', ← ad_apply (R := K), ← LieDerivation.coe_ad_apply_eq_ad_apply, hy, aux hz]
  /- Thus `y` belongs to `H` since `H` is self-normalizing. -/
  replace hy' : y ∈ H := by
    suffices y ∈ H.normalizer by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at this
    exact (H.mem_normalizer_iff y).mpr fun z hz ↦ hy' z hz ▸ LieSubalgebra.zero_mem H
  /- It suffices to show `x = y` since `S = ad K L y` is semisimple. -/
  suffices x = y by rwa [this, ← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rw [← sub_eq_zero]
  /- This will follow if we can show that `ad K L (x - y)` is nilpotent. -/
  apply eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra K L H (H.sub_mem hx hy')
  /- Which is true because `ad K L (x - y) = N`. -/
  replace hy : S = ad K L y := by rw [← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rwa [map_sub, hSN, hy, add_sub_cancel_right, eq_sub_of_add_eq hSN.symm]
/-
**LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.IsKilling`。
形式化陈述：lie_eq_smul_of_mem_rootSpace {α : H -> K} {x : L} (hx : x in rootSpace H α
) (h : H) : ⁅h, x⁆ = α h • x
参数：hx : x in rootSpace H α；h : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieModule.genWeightSpace_le_genWeightSpaceOf`：genWeightSpace_le_genWeigh
tSpaceOf (x : L) (χ : L -> R) : genWeightSpace M χ <= genWeightSpaceOf M (χ x) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`：∀ {R : T
ype u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : 
_root_.Module R M]   {f : Module.End R M}, f.IsFinit…
· 使用定理 `Module.End.IsSemisimple.isFinitelySemisimple`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   {f : Module.End R M}, f.IsSemis…
· 使用引理 `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`：isSemisi
mple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x in H) : (ad K L x).IsSemisimpl
e
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma lie_eq_smul_of_mem_rootSpace {α : H → K} {x : L} (hx : x ∈ rootSpace H α) (h : H) :
    ⁅h, x⁆ = α h • x := by
  replace hx : x ∈ (ad K L h).maxGenEigenspace (α h) :=
    genWeightSpace_le_genWeightSpaceOf L h α hx
  rw [(isSemisimple_ad_of_mem_isCartanSubalgebra
    h.property).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at hx
  simpa using hx
/-
**LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace
_neg** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg {α : Weight 
K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace H (-α)) : ⁅e, 
f⁆ = killingForm K L e f • (cartanEquivDual H).symm α
参数：heα : e in rootSpace H α；hfα : f in rootSpace H (-α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_roo
tSpace_neg_aux`：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_au
x {α : Weight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSp…
· 使用引理 `LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace`：lie_eq_smul_of_mem_ro
otSpace {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H) : ⁅h, x⁆ = α h • 
x
-/
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by
  apply lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα
  exact lie_eq_smul_of_mem_rootSpace heα
/-
**LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton'** 是 Mathlib 中的一个引理，位于命
名空间 `LieAlgebra.IsKilling`。
形式化陈述：coe_corootSpace_eq_span_singleton' (α : Weight K H L) : (corootSpace α).to
Submodule = K ∙ (cartanEquivDual H).symm α
参数：α : Weight K H L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_roo
tSpace_neg`：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg {α : W
eight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace …
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_span`：span_span : span R (span R s : Set M) = span R s
· 使用引理 `LieAlgebra.IsKilling.cartanEquivDual_symm_apply_mem_corootSpace`：cartanE
quivDual_symm_apply_mem_corootSpace (α : Weight K H L) : (cartanEquivDual H).sym
m α in corootSpace α
-/
lemma coe_corootSpace_eq_span_singleton' (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ (cartanEquivDual H).symm α := by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} ⊆
        K ∙ ((cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      exact ⟨killingForm K L e f, rfl⟩
    simp only [LieSubmodule.mem_toSubmodule, mem_corootSpace] at hx'
    replace this := Submodule.span_mono this hx'
    rw [Submodule.span_span] at this
    rw [Submodule.mem_span_singleton] at this ⊢
    obtain ⟨t, rfl⟩ := this
    solve_by_elim
  · simp only [Submodule.span_singleton_le_iff_mem, LieSubmodule.mem_toSubmodule]
    exact cartanEquivDual_symm_apply_mem_corootSpace α

end PerfectField

section CharZero

variable [CharZero K]

/-- The contrapositive of this result is very useful, taking `x` to be the element of `H`
corresponding to a root `α` under the identification between `H` and `H^*` provided by the Killing
form. -/
/-
**LieAlgebra.IsKilling.eq_zero_of_apply_eq_zero_of_mem_corootSpace** 是 Mathlib 中
的一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：eq_zero_of_apply_eq_zero_of_mem_corootSpace (x : H) (α : H -> K) (hαx : α 
x = 0) (hx : x in corootSpace α) : x = 0
参数：x : H；α : H -> K；hαx : α x = 0；hx : x in corootSpace α。
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
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.corootSpace_zero_eq_bot`：corootSpace_zero_eq_bot : 
corootSpace (0 : H -> K) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
· 使用引理 `LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero`：exists_forall_
mem_corootSpace_smul_add_eq_zero [IsDomain R] [IsPrincipalIdealRing R] [CharZero
 R] [Module.IsTorsionFree R M] [IsNoetherian R…
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The contrapositive of this result is very useful, taking `x` to be the element o
f `H`
corresponding to a root `α` under the identification between `H` and `H^*` provi
ded by the Killing
form.
-/
lemma eq_zero_of_apply_eq_zero_of_mem_corootSpace
    (x : H) (α : H → K) (hαx : α x = 0) (hx : x ∈ corootSpace α) :
    x = 0 := by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x ∈ ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β ↦ ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx
/-
**LieAlgebra.IsKilling.disjoint_ker_weight_corootSpace** 是 Mathlib 中的一个引理，位于命名空间
 `LieAlgebra.IsKilling`。
形式化陈述：disjoint_ker_weight_corootSpace (α : Weight K H L) : Disjoint α.ker (coroo
tSpace α)
参数：α : Weight K H L。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用引理 `LieAlgebra.IsKilling.eq_zero_of_apply_eq_zero_of_mem_corootSpace`：eq_zer
o_of_apply_eq_zero_of_mem_corootSpace (x : H) (α : H -> K) (hαx : α x = 0) (hx :
 x in corootSpace α) : x = 0
-/
lemma disjoint_ker_weight_corootSpace (α : Weight K H L) :
    Disjoint α.ker (corootSpace α) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ ↦ ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx
/-
**LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero** 是 Mathlib 中的一个引
理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZe
ro) : α ((cartanEquivDual H).symm α) != 0
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
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
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用引理 `LieAlgebra.IsKilling.cartanEquivDual_symm_apply_mem_corootSpace`：cartanE
quivDual_symm_apply_mem_corootSpace (α : Weight K H L) : (cartanEquivDual H).sym
m α in corootSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用引理 `LieAlgebra.IsKilling.disjoint_ker_weight_corootSpace`：disjoint_ker_weigh
t_corootSpace (α : Weight K H L) : Disjoint α.ker (corootSpace α)
-/
lemma root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    α ((cartanEquivDual H).symm α) ≠ 0 := by
  contrapose hα
  suffices (cartanEquivDual H).symm α ∈ α.ker ⊓ corootSpace α by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, cartanEquivDual_symm_apply_mem_corootSpace α⟩
/-
**LieAlgebra.IsKilling.root_apply_coroot** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.I
sKilling`。
形式化陈述：root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) : α (coroot α) = 2
参数：hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.Weight.coe_coe`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4}
 [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : 
AddCommGroup M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero`：root_apply
_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) : α ((cartan
EquivDual H).symm α) != 0
-/
lemma root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) :
    α (coroot α) = 2 := by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel₀ (root_apply_cartanEquivDual_symm_ne_zero hα)
/-
**LieAlgebra.IsKilling.coroot_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.
IsKilling`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] {H : LieSubalgebra K L}
 [inst_4 : H.IsCartanSubalgebra]   [inst_5 : LieAlgebra.IsKilling K L] [LieModul
e.IsTriangularizable K (↥H) L] [CharZero K]   {α : LieModule.Weight K (↥H) L}, L
ieAlgebra.IsKilling.coroot α = 0 ↔ α.IsZero
参数：↥H；↥H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieModule.Weight.coe_toLinear_eq_zero_iff`：∀ {R : Type u_2} {L : Type u_
3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra 
R L]   [inst_3 : AddCommGroup M…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
（共 31 条，此处仅展示前 30 条）
-/
@[simp] lemma coroot_eq_zero_iff {α : Weight K H L} :
    coroot α = 0 ↔ α.IsZero := by
  refine ⟨fun hα ↦ ?_, fun hα ↦ ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

@[simp]
/-
**LieAlgebra.IsKilling.coroot_zero** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsKilli
ng`。
形式化陈述：coroot_zero [Nontrivial L] : coroot (0 : Weight K H L) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LieAlgebra.instNontrivialSubtypeMemLieSubmoduleLieSubalgebraGenWeightSpa
ceOfNatForall`：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra R L) [inst_3 : LieRi…
· 使用定理 `LieSubalgebra.instNontrivialSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type 
u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R 
L] [Nontrivial L]   (H : LieSubalgebra R L) [H.I…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma coroot_zero [Nontrivial L] : coroot (0 : Weight K H L) = 0 := by simp [Weight.isZero_zero]
/-
**LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton** 是 Mathlib 中的一个引理，位于命名
空间 `LieAlgebra.IsKilling`。
形式化陈述：coe_corootSpace_eq_span_singleton (α : Weight K H L) : (corootSpace α).toS
ubmodule = K ∙ coroot α
参数：α : Weight K H L。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.corootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst
 : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   {H : LieSubalgeb
ra R L} [inst_3 : LieRi…
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用引理 `LieAlgebra.IsKilling.corootSpace_zero_eq_bot`：corootSpace_zero_eq_bot : 
corootSpace (0 : H -> K) = ⊥
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
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero`：root_apply
_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) : α ((cartan
EquivDual H).symm α) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）
-/
lemma coe_corootSpace_eq_span_singleton (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ coroot α := by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (cartanEquivDual H).symm α
    suffices (K ∙ coroot α) = K ∙ α' by rw [coe_corootSpace_eq_span_singleton']; exact this.symm
    have : IsUnit (2 * (α α')⁻¹) := by simpa using root_apply_cartanEquivDual_symm_ne_zero hα
    change (K ∙ (2 • (α α')⁻¹ • α')) = _
    simpa [← Nat.cast_smul_eq_nsmul K, smul_smul] using Submodule.span_singleton_smul_eq this _
/-
**LieAlgebra.IsKilling.eq_coroot_of_mem_corootSpace_of_two** 是 Mathlib 中的一个引理，位于
命名空间 `LieAlgebra.IsKilling`。
形式化陈述：eq_coroot_of_mem_corootSpace_of_two (α : Weight K H L) {x : H} (h_mem : x 
in corootSpace α) (h_two : α x = 2) : x = coroot α
参数：α : Weight K H L；h_mem : x in corootSpace α；h_two : α x = 2。
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton`：coe_corootSpace_
eq_span_singleton (α : Weight K H L) : (corootSpace α).toSubmodule = K ∙ coroot 
α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
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
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_coroot_of_mem_corootSpace_of_two (α : Weight K H L) {x : H}
    (h_mem : x ∈ corootSpace α) (h_two : α x = 2) :
    x = coroot α := by
  by_cases h₀ : α.IsZero; · simp [h₀.eq] at h_two
  replace h_mem : x ∈ K ∙ coroot α := by rwa [← coe_corootSpace_eq_span_singleton]
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h_mem
  suffices t = 1 by simp [this]
  simpa [root_apply_coroot h₀] using h_two

@[simp]
/-
**LieAlgebra.IsKilling.corootSpace_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra.IsKilling`。
形式化陈述：corootSpace_eq_bot_iff {α : Weight K H L} : corootSpace α = ⊥ ↔ α.IsZero
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton`：coe_corootSpace_
eq_span_singleton (α : Weight K H L) : (corootSpace α).toSubmodule = K ∙ coroot 
α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma corootSpace_eq_bot_iff {α : Weight K H L} :
    corootSpace α = ⊥ ↔ α.IsZero := by
  simp [← LieSubmodule.toSubmodule_eq_bot, coe_corootSpace_eq_span_singleton α]
/-
**LieAlgebra.IsKilling.isCompl_ker_weight_span_coroot** 是 Mathlib 中的一个引理，位于命名空间 
`LieAlgebra.IsKilling`。
形式化陈述：isCompl_ker_weight_span_coroot (α : Weight K H L) : IsCompl α.ker (K ∙ cor
oot α)
参数：α : Weight K H L。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieModule.Weight.coe_toLinear_eq_zero_iff`：∀ {R : Type u_2} {L : Type u_
3} {M : Type u_4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra 
R L]   [inst_3 : AddCommGroup M…
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieAlgebra.IsKilling.coroot_eq_zero_iff`：∀ {K : Type u_2} {L : Type u_3}
 [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : Fin
iteDimensional K L] {H : LieS…
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `isCompl_top_bot`：isCompl_top_bot : IsCompl (⊤ : α) ⊥
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton`：coe_corootSpace_
eq_span_singleton (α : Weight K H L) : (corootSpace α).toSubmodule = K ∙ coroot 
α
· 使用引理 `Module.Dual.isCompl_ker_of_disjoint_of_ne_bot`：isCompl_ker_of_disjoint_o
f_ne_bot {p : Submodule K V₁} (hpf : Disjoint (LinearMap.ker f) p) (hp : p != ⊥)
 : IsCompl (LinearMap.ker f) p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用引理 `LieAlgebra.IsKilling.disjoint_ker_weight_corootSpace`：disjoint_ker_weigh
t_corootSpace (α : Weight K H L) : Disjoint α.ker (corootSpace α)
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
（共 31 条，此处仅展示前 30 条）
-/
lemma isCompl_ker_weight_span_coroot (α : Weight K H L) :
    IsCompl α.ker (K ∙ coroot α) := by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by simp_all)
      (disjoint_ker_weight_corootSpace α)
    replace hα : corootSpace α ≠ ⊥ := by simpa using hα
    rwa [ne_eq, ← LieSubmodule.toSubmodule_inj] at hα
/-
**LieAlgebra.IsKilling.traceForm_eq_zero_of_mem_ker_of_mem_span_coroot** 是 Mathl
ib 中的一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：traceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : 
H} (hx : x in α.ker) (hy : y in K ∙ coroot α) : traceForm K H L x y = 0
参数：hx : x in α.ker；hy : y in K ∙ coroot α。
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
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.traceForm_apply_lie_apply`：traceForm_apply_lie_apply (x y z : 
L) : traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用引理 `LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace`：lie_eq_smul_of_mem_ro
otSpace {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H) : ⁅h, x⁆ = α h • 
x
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
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
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 35 条，此处仅展示前 30 条）
-/
lemma traceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : H}
    (hx : x ∈ α.ker) (hy : y ∈ K ∙ coroot α) :
    traceForm K H L x y = 0 := by
  rw [← coe_corootSpace_eq_span_singleton, LieSubmodule.mem_toSubmodule, mem_corootSpace'] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, v, -, huv⟩ := hz
    change killingForm K L (x : L) (z : L) = 0
    replace hx : α x = 0 := by simpa using hx
    rw [← huv, ← traceForm_apply_lie_apply, ← LieSubalgebra.coe_bracket_of_module,
      lie_eq_smul_of_mem_rootSpace hu, hx, zero_smul, map_zero, LinearMap.zero_apply]
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul _ _ _ hz => simp [hz]
/-
**LieAlgebra.IsKilling.orthogonal_span_coroot_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra.IsKilling`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] {H : LieSubalgebra K L}
 [inst_4 : H.IsCartanSubalgebra]   [inst_5 : LieAlgebra.IsKilling K L] [LieModul
e.IsTriangularizable K (↥H) L] [inst_7 : CharZero K]   (α : LieModule.Weight K (
↥H) L),   (LieModule.traceForm K (↥H) L).orthogonal (K ∙ LieAlgebra.IsKilling.co
root α) = LieModule.Weight.ker
参数：↥H；α : LieModule.Weight K (↥H) L；LieModule.traceForm K (↥H) L；K ∙ LieAlgebra.
IsKilling.coroot α。
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
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `LinearMap.BilinForm.orthogonal_bot`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B
 : LinearMap.BilinForm R…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `LieAlgebra.IsKilling.traceForm_coroot`：traceForm_coroot (α : Weight K H 
L) (x : H) : traceForm K H L (coroot α) x = 2 • (α <| (cartanEquivDual H).symm α
)⁻¹ • α x
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
（共 36 条，此处仅展示前 30 条）
-/
@[simp] lemma orthogonal_span_coroot_eq_ker (α : Weight K H L) :
    (traceForm K H L).orthogonal (K ∙ coroot α) = α.ker := by
  if hα : α.IsZero then
    have hα' : coroot α = 0 := by simpa
    replace hα : α.ker = ⊤ := by ext; simp [hα]
    simp [hα, hα']
  else
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx y hy ↦ ?_)
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      specialize hx (coroot α) (Submodule.mem_span_singleton_self _)
      simp only [traceForm_coroot, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, false_or] at hx
      simpa using hx.resolve_left (root_apply_cartanEquivDual_symm_ne_zero hα)
    · have := traceForm_eq_zero_of_mem_ker_of_mem_span_coroot hx hy
      rwa [traceForm_comm] at this
/-
**LieAlgebra.IsKilling.coroot_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.IsKil
ling`。
形式化陈述：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing L] [inst_1 : Field K] [ins
t_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K L] {H : LieSubalgebra K L}
 [inst_4 : H.IsCartanSubalgebra]   [inst_5 : LieAlgebra.IsKilling K L] [LieModul
e.IsTriangularizable K (↥H) L] [CharZero K]   (α β : LieModule.Weight K (↥H) L),
 LieAlgebra.IsKilling.coroot α = LieAlgebra.IsKilling.coroot β ↔ α = β
参数：↥H；α β : LieModule.Weight K (↥H) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.IsKilling.coroot_eq_zero_iff`：∀ {K : Type u_2} {L : Type u_3}
 [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : Fin
iteDimensional K L] {H : LieS…
· 使用定理 `LieModule.Weight.ext`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_4} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddC
ommGroup M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModule.Weight.IsZero.eq`：∀ {R : Type u_2} {L : Type u_3} {M : Type u_
4} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 
: AddCommGroup M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
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
· 使用定理 `LieAlgebra.IsKilling.orthogonal_span_coroot_eq_ker`：∀ {K : Type u_2} {L 
: Type u_3} [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [i
nst_3 : FiniteDimensional K L] {H : LieS…
· 使用引理 `Module.Dual.eq_of_ker_eq_of_apply_eq`：eq_of_ker_eq_of_apply_eq [FiniteDi
mensional K V₁] {f g : Module.Dual K V₁} (x : V₁) (h : LinearMap.ker f = LinearM
ap.ker g) (h' : f x = g x)…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `LieModule.Weight.toLinear_apply`：∀ (R : Type u_2) (L : Type u_3) (M : Ty
pe u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [in
st_3 : AddCommGroup M…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `LieAlgebra.IsKilling.root_apply_coroot`：root_apply_coroot {α : Weight K 
H L} (hα : α.IsNonZero) : α (coroot α) = 2
（共 33 条，此处仅展示前 30 条）
-/
@[simp] lemma coroot_eq_iff (α β : Weight K H L) :
    coroot α = coroot β ↔ α = β := by
  refine ⟨fun hyp ↦ ?_, fun h ↦ by rw [h]⟩
  if hα : α.IsZero then
    have hβ : β.IsZero := by
      rw [← coroot_eq_zero_iff] at hα ⊢
      rwa [← hyp]
    ext
    simp [hα.eq, hβ.eq]
  else
    have hβ : β.IsNonZero := by
      contrapose hα
      simp only [← coroot_eq_zero_iff] at hα ⊢
      rwa [hyp]
    have : α.ker = β.ker := by
      rw [← orthogonal_span_coroot_eq_ker α, hyp, orthogonal_span_coroot_eq_ker]
    suffices (α : H →ₗ[K] K) = β by ext x; simpa using LinearMap.congr_fun this x
    apply Module.Dual.eq_of_ker_eq_of_apply_eq (coroot α) this
    · rw [Weight.toLinear_apply, root_apply_coroot hα, hyp, Weight.toLinear_apply,
        root_apply_coroot hβ]
    · simp [root_apply_coroot hα]
/-
**LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero** 是 Mathlib 中的一个引理
，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZer
o) : exists h e f : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f in rootSpace H
 (-α)
参数：hα : α.IsNonZero。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieModule.Weight.exists_ne_zero`：exists_ne_zero (χ : Weight R L M) : exi
sts x in genWeightSpace M χ, x != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.IsKilling.ker_killingForm_eq_bot`：∀ (R : Type u_1) (L : Type 
u_3) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAl
gebra.IsKilling R L], LinearMap.k…
· 使用引理 `LieAlgebra.mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg`
：mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg {α : H -> K} {x : 
L} (hx : x in rootSpace H α) (hx' : forall y in rootSpace H (…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用引理 `LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_roo
tSpace_neg`：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg {α : W
eight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace …
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Submodule.coe_smul_of_tower`：coe_smul_of_tower [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (x : p) : ((r • x : p) : M) = r • (x : M)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
（共 57 条，此处仅展示前 30 条）
-/
lemma exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ h e f : L, IsSl2Triple h e f ∧ e ∈ rootSpace H α ∧ f ∈ rootSpace H (-α) := by
  obtain ⟨e, heα : e ∈ rootSpace H α, he₀ : e ≠ 0⟩ := α.exists_ne_zero
  obtain ⟨f', hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  let h : H := ⟨⁅e, f'⁆, hef ▸ Submodule.smul_mem _ _ (Submodule.coe_mem _)⟩
  have hh : α h ≠ 0 := by
    have : h = killingForm K L e f' • (cartanEquivDual H).symm α := by
      simp only [h, Subtype.ext_iff, hef]
      rw [Submodule.coe_smul_of_tower]
    rw [this, map_smul, smul_eq_mul, ne_eq, mul_eq_zero, not_or]
    exact ⟨hf, root_apply_cartanEquivDual_symm_ne_zero hα⟩
  let f := (2 * (α h)⁻¹) • f'
  replace hef : ⁅⁅e, f⁆, e⁆ = 2 • e := by
    have : ⁅⁅e, f'⁆, e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    rw [lie_smul, smul_lie, this, ← smul_assoc, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hh,
      mul_one, two_smul, two_smul]
  refine ⟨⁅e, f⁆, e, f, ⟨fun contra ↦ ?_, rfl, hef, ?_⟩, heα, Submodule.smul_mem _ _ hfα⟩
  · rw [contra] at hef
    have : IsAddTorsionFree L := .of_isTorsionFree K L
    simp only [zero_lie, eq_comm (a := (0 : L)), smul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hef
    contradiction
  · have : ⁅⁅e, f'⁆, f'⁆ = - α h • f' := lie_eq_smul_of_mem_rootSpace hfα h
    rw [lie_smul, lie_smul, smul_lie, this]
    simp [← smul_assoc, f, hh, mul_comm _ (2 * (α h)⁻¹)]
/-
**LieAlgebra.IsKilling._root_.IsSl2Triple.h_eq_coroot** 是 Mathlib 中的一个引理，位于命名空间 
`LieAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsSl2Triple.h_eq_coroot {α : Weight K H L} (hα : α.IsNonZero)
    {h e f : L} (ht : IsSl2Triple h e f) (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) :
    h = coroot α := by
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift h to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  congr 1
  have key : α h = 2 := by
    have := lie_eq_smul_of_mem_rootSpace heα h
    rw [LieSubalgebra.coe_bracket_of_module, ht.lie_h_e_smul K] at this
    exact smul_left_injective K ht.e_ne_zero this.symm
  suffices ∃ s : K, s • h = coroot α by
    obtain ⟨s, hs⟩ := this
    replace this : s = 1 := by simpa [root_apply_coroot hα, key] using congr_arg α hs
    rwa [this, one_smul] at hs
  set α' := (cartanEquivDual H).symm α with hα'
  have h_eq : h = killingForm K L e f • α' := by
    simp only [hα', Subtype.ext_iff, ← ht.lie_e_f, hef]
    rw [Submodule.coe_smul_of_tower]
  use (2 • (α α')⁻¹) * (killingForm K L e f)⁻¹
  have hef₀ : killingForm K L e f ≠ 0 := by
    have := ht.h_ne_zero
    contrapose this
    simpa [this] using h_eq
  rw [h_eq, smul_smul, mul_assoc, inv_mul_cancel₀ hef₀, mul_one, smul_assoc, coroot]
/-
**LieAlgebra.IsKilling.finrank_rootSpace_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `LieAl
gebra.IsKilling`。
形式化陈述：finrank_rootSpace_eq_one (α : Weight K H L) (hα : α.IsNonZero) : finrank K
 (rootSpace H α) = 1
参数：α : Weight K H L；hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero`：exists_isSl
2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : exists h e f
 : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f …
· 使用引理 `LinearMap.ker_ne_bot_of_finrank_lt`：ker_ne_bot_of_finrank_lt [FiniteDime
nsional K V] [FiniteDimensional K V₂] {f : V ->ₗ[K] V₂} (h : finrank K V₂ < finr
ank K V) : LinearMap.ker…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieModule.traceForm_comm`：traceForm_comm (x y : L) : traceForm R L M x y
 = traceForm R L M y x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `LieAlgebra.IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_roo
tSpace_neg`：lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg {α : W
eight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace …
· 使用引理 `IsSl2Triple.symm`：symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e w
here h_ne_zero
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 47 条，此处仅展示前 30 条）
-/
lemma finrank_rootSpace_eq_one (α : Weight K H L) (hα : α.IsNonZero) :
    finrank K (rootSpace H α) = 1 := by
  suffices ¬ 1 < finrank K (rootSpace H α) by
    have h₀ : finrank K (rootSpace H α) ≠ 0 := by
      convert_to! finrank K (rootSpace H α).toSubmodule ≠ 0
      simpa using! α.genWeightSpace_ne_bot
    lia
  intro contra
  obtain ⟨h, e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  let F : rootSpace H α →ₗ[K] K := killingForm K L f ∘ₗ (rootSpace H α).subtype
  have hF : LinearMap.ker F ≠ ⊥ := F.ker_ne_bot_of_finrank_lt <| by rwa [finrank_self]
  obtain ⟨⟨y, hyα⟩, hy, hy₀⟩ := (Submodule.ne_bot_iff _).mp hF
  replace hy : ⁅y, f⁆ = 0 := by
    have : killingForm K L y f = 0 := by simpa [F, traceForm_comm] using! hy
    simpa [this] using! lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg hyα hfα
  have P : ht.symm.HasPrimitiveVectorWith y (-2 : K) :=
    { ne_zero := by simpa [LieSubmodule.mk_eq_zero] using! hy₀
      lie_h := by simp only [neg_smul, neg_lie, ht.h_eq_coroot hα heα hfα,
        ← H.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace hyα (coroot α),
        root_apply_coroot hα]
      lie_e := by rw [← lie_skew, hy, neg_zero] }
  obtain ⟨n, hn⟩ := P.exists_nat
  assumption_mod_cast

/-- The embedded `sl₂` associated to a root. -/
/-
**LieAlgebra.IsKilling.sl2SubalgebraOfRoot** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra
.IsKilling`。
形式化陈述：sl2SubalgebraOfRoot {α : Weight K H L} (hα : α.IsNonZero) : LieSubalgebra 
K L
参数：hα : α.IsNonZero。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero`：exists_isSl
2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : exists h e f
 : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f …

--- 原说明 ---
The embedded `sl₂` associated to a root.
-/
noncomputable def sl2SubalgebraOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubalgebra K L := by
  choose h e f t ht using exists_isSl2Triple_of_weight_isNonZero hα
  exact t.toLieSubalgebra K
/-
**LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Li
eAlgebra.IsKilling`。
形式化陈述：mem_sl2SubalgebraOfRoot_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f :
 L} (t : IsSl2Triple h e f) (hte : e in rootSpace H α) (htf : f in rootSpace H (
-α)) {x : L} : x in sl2SubalgebraOfRoot hα ↔ exists c₁ c₂ c₃ : K, x = c₁ • e + c
₂ • f + c₃ • ⁅e, f⁆
参数：hα : α.IsNonZero；t : IsSl2Triple h e f；hte : e in rootSpace H α；htf : f in ro
otSpace H (-α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用引理 `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero`：exists_isSl
2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : exists h e f
 : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用引理 `IsSl2Triple.e_ne_zero`：e_ne_zero (t : IsSl2Triple h e f) : e != 0
· 使用引理 `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`：finrank_rootSpace_eq_one 
(α : Weight K H L) (hα : α.IsNonZero) : finrank K (rootSpace H α) = 1
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsSl2Triple.f_ne_zero`：f_ne_zero (t : IsSl2Triple h e f) : f != 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mem_sl2SubalgebraOfRoot_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
    (t : IsSl2Triple h e f) (hte : e ∈ rootSpace H α) (htf : f ∈ rootSpace H (-α)) {x : L} :
    x ∈ sl2SubalgebraOfRoot hα ↔ ∃ c₁ c₂ c₃ : K, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp only [sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : ∃ c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨_, he.choose_spec.choose_spec.2.1⟩
    exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨cf, hcf⟩ : ∃ c : K, hf.choose = c • f := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, htf⟩ (by simpa using t.f_ne_zero)).mp
      (finrank_rootSpace_eq_one (-α) (by simpa)) ⟨_, hf.choose_spec.2.2⟩
    exact ⟨c, by simpa using hc.symm⟩
  have hce₀ : ce ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hce
    exact he.choose_spec.choose_spec.1.e_ne_zero hce
  have hcf₀ : cf ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hcf
    exact he.choose_spec.choose_spec.1.f_ne_zero hcf
  simp_rw [hcf, hce]
  refine ⟨fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce, c₂ * cf, c₃ * cf * ce, ?_⟩,
    fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce⁻¹, c₂ * cf⁻¹, c₃ * ce⁻¹ * cf⁻¹, ?_⟩⟩
  · simp [hx, mul_smul]
  · simp [hx, mul_smul, hce₀, hcf₀]

/-- The `sl₂` subalgebra associated to a root, regarded as a Lie submodule over the Cartan
subalgebra. -/
/-
**LieAlgebra.IsKilling.sl2SubmoduleOfRoot** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.
IsKilling`。
形式化陈述：sl2SubmoduleOfRoot {α : Weight K H L} (hα : α.IsNonZero) : LieSubmodule K 
H L where __
参数：hα : α.IsNonZero。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `sl₂` subalgebra associated to a root, regarded as a Lie submodule over the 
Cartan
subalgebra.
-/
noncomputable def sl2SubmoduleOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubmodule K H L where
  __ := sl2SubalgebraOfRoot hα
  lie_mem {h} x hx := by
    suffices ⁅(h : L), x⁆ ∈ sl2SubalgebraOfRoot hα by simpa
    obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    replace hx : x ∈ sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα, lie_add, lie_add, lie_smul, lie_smul, lie_smul]
    have he_wt : ⁅(h : L), e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    have hf_wt : ⁅(h : L), f⁆ = (-α) h • f := lie_eq_smul_of_mem_rootSpace hfα h
    have hef_zero : ⁅(h : L), ⁅e, f⁆⁆ = 0 := by
      suffices h_coroot_in_zero : ⁅e, f⁆ ∈ rootSpace H (0 : H → K) from
        lie_eq_smul_of_mem_rootSpace h_coroot_in_zero h ▸ (zero_smul K ⁅e, f⁆)
      rw [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, rootSpace_zero_eq K L H]
      exact (coroot α).property
    exact ⟨c₁ * α h, c₂ * (-α h), 0, by simp [he_wt, hf_wt, hef_zero, smul_smul]⟩

/-- The coroot space of `α` viewed as a submodule of the ambient Lie algebra `L`.
This represents the image of the coroot space under the inclusion `H ↪ L`. -/
/-
**LieAlgebra.IsKilling.corootSubmodule** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra.I
sKilling`。
形式化陈述：corootSubmodule (α : Weight K H L) : LieSubmodule K H L
参数：α : Weight K H L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coroot space of `α` viewed as a submodule of the ambient Lie algebra `L`.
This represents the image of the coroot space under the inclusion `H ↪ L`.
-/
noncomputable abbrev corootSubmodule (α : Weight K H L) : LieSubmodule K H L :=
  LieSubmodule.map H.toLieSubmodule.incl (corootSpace α)

omit [CharZero K] in
/-
**LieAlgebra.IsKilling.coe_coroot_mem_corootSubmodule** 是 Mathlib 中的一个引理，位于命名空间 
`LieAlgebra.IsKilling`。
形式化陈述：coe_coroot_mem_corootSubmodule (α : Weight K H L) : (coroot α : L) in coro
otSubmodule α
参数：α : Weight K H L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.mem_map`：mem_map (m' : M') : m' in N.map f ↔ exists m, m in
 N ∧ f m = m'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LieAlgebra.IsKilling.coroot_mem_corootSpace`：∀ {K : Type u_2} {L : Type 
u_3} [inst : LieRing L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 :
 FiniteDimensional K L] {H : LieS…
-/
lemma coe_coroot_mem_corootSubmodule (α : Weight K H L) :
    (coroot α : L) ∈ corootSubmodule α :=
  (LieSubmodule.mem_map _).mpr
    ⟨⟨coroot α, (coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
open Submodule in
/-
**LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra.IsKilling`。
形式化陈述：sl2SubmoduleOfRoot_eq_sup (α : Weight K H L) (hα : α.IsNonZero) : sl2Submo
duleOfRoot hα = genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α
参数：α : Weight K H L；hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用引理 `LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero`：exists_isSl
2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) : exists h e f
 : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff`：mem_sl2SubalgebraOfRoo
t_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f : L} (t : IsSl2Triple h e f) 
(hte : e in rootSpace H α) (htf : f in…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSl2Triple.h_eq_coroot`：∀ {K : Type u_2} {L : Type u_3} [inst : LieRing
 L] [inst_1 : Field K] [inst_2 : LieAlgebra K L]   [inst_3 : FiniteDimensional K
 L] {H : LieS…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Submodule.subtype_apply`：subtype_apply (x : p) : p.subtype x = x
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `LieSubmodule.mk_eq_zero`：mk_eq_zero {x} (h : x in N) : (⟨x, h⟩ : N) = 0 
↔ x = 0
· 使用引理 `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`：finrank_rootSpace_eq_one 
(α : Weight K H L) (hα : α.IsNonZero) : finrank K (rootSpace H α) = 1
（共 38 条，此处仅展示前 30 条）
-/
lemma sl2SubmoduleOfRoot_eq_sup (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα = genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α := by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · replace hx : x ∈ sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
    · exact mem_sup_left <| mem_sup_left <| smul_mem _ _ heα
    · exact mem_sup_left <| mem_sup_right <| smul_mem _ _ hfα
    · suffices ∃ y ∈ corootSpace α, H.subtype y = c₃ • h' from
        mem_sup_right <| by simpa [ht.lie_e_f, -Subtype.exists]
      refine ⟨c₃ • coroot α, smul_mem _ _ <| by simp, ?_⟩
      rw [IsSl2Triple.h_eq_coroot hα ht heα hfα, map_smul, subtype_apply]
  · have aux {β : Weight K H L} (hβ : β.IsNonZero) {y g : L}
        (hy : y ∈ genWeightSpace L β) (hg : g ∈ rootSpace H β) (hg_ne_zero : g ≠ 0) :
        ∃ c : K, y = c • g := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨g, hg⟩
        (by rwa [ne_eq, LieSubmodule.mk_eq_zero])).mp (finrank_rootSpace_eq_one β hβ) ⟨y, hy⟩
      exact ⟨c, by simpa using hc.symm⟩
    obtain ⟨x_αneg, hx_αneg, x_h, ⟨y, hy_coroot, rfl⟩, rfl⟩ := mem_sup.mp hx
    obtain ⟨x_pos, hx_pos, x_neg, hx_neg, rfl⟩ := mem_sup.mp hx_αneg
    obtain ⟨c₁, rfl⟩ := aux hα hx_pos heα ht.e_ne_zero
    obtain ⟨c₂, rfl⟩ := aux (Weight.IsNonZero.neg hα) hx_neg hfα ht.f_ne_zero
    obtain ⟨c₃, rfl⟩ : ∃ c₃ : K, c₃ • coroot α = y := by
      simpa [← mem_span_singleton, ← coe_corootSpace_eq_span_singleton α]
    change _ ∈ sl2SubalgebraOfRoot hα
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
    use c₁, c₂, c₃
    simp [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, -LieSubmodule.incl_coe]
/-
**LieAlgebra.IsKilling.sl2SubmoduleOfRoot_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieA
lgebra.IsKilling`。
形式化陈述：sl2SubmoduleOfRoot_ne_bot (α : Weight K H L) (hα : α.IsNonZero) : sl2Submo
duleOfRoot hα != ⊥
参数：α : Weight K H L；hα : α.IsNonZero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.IsKilling.sl2SubmoduleOfRoot_eq_sup`：sl2SubmoduleOfRoot_eq_su
p (α : Weight K H L) (hα : α.IsNonZero) : sl2SubmoduleOfRoot hα = genWeightSpace
 L α ⊔ genWeightSpace L (-α) ⊔ coroo…
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用引理 `LieModule.Weight.genWeightSpace_ne_bot`：genWeightSpace_ne_bot (χ : Weigh
t R L M) : genWeightSpace M χ != ⊥
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma sl2SubmoduleOfRoot_ne_bot (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα ≠ ⊥ := by
  rw [sl2SubmoduleOfRoot_eq_sup]
  exact ne_bot_of_le_ne_bot α.genWeightSpace_ne_bot (le_sup_of_le_left le_sup_left)

/-- The collection of roots as a `Finset`. -/
/-
**LieAlgebra.IsKilling._root_.LieSubalgebra.root** 是 Mathlib 中的一个缩写定义，位于命名空间 `Li
eAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of roots as a `Finset`.
-/
noncomputable abbrev _root_.LieSubalgebra.root : Finset (Weight K H L) := {α | α.IsNonZero}

omit [IsKilling K L] [IsTriangularizable K H L] [CharZero K] in
@[simp]
/-
**LieAlgebra.IsKilling._root_.LieSubalgebra.isNonZero_coe_root** 是 Mathlib 中的一个引
理，位于命名空间 `LieAlgebra.IsKilling`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LieSubalgebra.isNonZero_coe_root (α : H.root) : (α : Weight K H L).IsNonZero := by
  aesop
/-
**LieAlgebra.IsKilling.restrict_killingForm_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Li
eAlgebra.IsKilling`。
形式化陈述：restrict_killingForm_eq_sum : (killingForm K L).restrict H = ∑ α in H.root
, (α : H ->ₗ[K] K).smulRight (α : H ->ₗ[K] K)
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
· 使用引理 `LieAlgebra.restrict_killingForm`：restrict_killingForm (H : LieSubalgebra
 R L) : (killingForm R L).restrict H = LieModule.traceForm R H L
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieModule.traceForm_eq_sum_finrank_nsmul'`：traceForm_eq_sum_finrank_nsmu
l' : traceForm K L M = ∑ χ in {χ : Weight K L M | χ.IsNonZero}, finrank K (genWe
ightSpace M χ) • (χ : L ->ₗ[K] …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`：finrank_rootSpace_eq_one 
(α : Weight K H L) (hα : α.IsNonZero) : finrank K (rootSpace H α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_killingForm_eq_sum :
    (killingForm K L).restrict H = ∑ α ∈ H.root, (α : H →ₗ[K] K).smulRight (α : H →ₗ[K] K) := by
  rw [restrict_killingForm, traceForm_eq_sum_finrank_nsmul' K H L]
  refine Finset.sum_congr rfl fun χ hχ ↦ ?_
  replace hχ : χ.IsNonZero := by simpa [LieSubalgebra.root] using hχ
  simp [finrank_rootSpace_eq_one _ hχ]

/-- In a Lie algebra with non-degenerate Killing form, a Lie ideal decomposes as its intersection
with the Cartan subalgebra plus a sum of root spaces corresponding to some subset of roots. -/
/-
**LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace** 是 Mathlib 中的
一个引理，位于命名空间 `LieAlgebra.IsKilling`。
形式化陈述：lieIdeal_eq_inf_cartan_sup_biSup_rootSpace (I : LieIdeal K L) : I.restr H 
= (I.restr H ⊓ H.toLieSubmodule) ⊔ ⨆ (α : H.root) (_ : rootSpace H α.val <= I.re
str H), rootSpace H α.val
参数：I : LieIdeal K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.instIsNilpotentSubtypeMemOfIsCartanSubalgebra`：∀ {R : Type
 u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R
 L] (H : LieSubalgebra R L)   [H.IsCartanSubalgeb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace`：lieIdeal_eq_i
nf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) : I.restr H = (I.restr H ⊓ 
H.toLieSubmodule) ⊔ ⨆ α : Weight K H L, ⨆ (_ : …
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Submodule.isAtom_iff_finrank_eq_one`：Submodule.isAtom_iff_finrank_eq_one
 {S : Submodule K V} : IsAtom S ↔ finrank K S = 1
· 使用引理 `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`：finrank_rootSpace_eq_one 
(α : Weight K H L) (hα : α.IsNonZero) : finrank K (rootSpace H α) = 1
· 使用定理 `LieSubmodule.toSubmodule_injective`：toSubmodule_injective : Function.Inj
ective (toSubmodule : LieSubmodule R L M -> Submodule R M)
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsAtom.not_le_iff_disjoint`：IsAtom.not_le_iff_disjoint (ha : IsAtom a) :
 ¬ a <= b ↔ Disjoint a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
In a Lie algebra with non-degenerate Killing form, a Lie ideal decomposes as its
 intersection
with the Cartan subalgebra plus a sum of root spaces corresponding to some subse
t of roots.
-/
lemma lieIdeal_eq_inf_cartan_sup_biSup_rootSpace (I : LieIdeal K L) :
    I.restr H = (I.restr H ⊓ H.toLieSubmodule) ⊔
      ⨆ (α : H.root) (_ : rootSpace H α.val ≤ I.restr H), rootSpace H α.val := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ hα ↦ hα))
  conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace]
  refine sup_le_sup_left (iSup₂_le fun α hα ↦ ?_) _
  by_cases h : rootSpace H α ≤ I.restr H
  · exact le_iSup₂_of_le ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩ h inf_le_right
  · have ha := Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_rootSpace_eq_one α hα)
    have : I.restr H ⊓ rootSpace H (α : H → K) = ⊥ :=
      LieSubmodule.toSubmodule_injective ((ha.not_le_iff_disjoint.mp h).symm.eq_bot)
    simp only [this, bot_le]

end CharZero

end IsKilling

end LieAlgebra

