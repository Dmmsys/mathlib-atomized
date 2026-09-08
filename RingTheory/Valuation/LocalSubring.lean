/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring

-- The copyright notice exceeds the maximum column width, but the `linter.style.header` linter
-- flags the copyright notice if "All rights reserved." is not on the same line as "Copyright".
set_option linter.style.header false

/-!

# Valuation subrings are exactly the maximal local subrings

See `LocalSubring.isMax_iff`.
Note that the order on local subrings is not merely inclusion but domination.

-/

@[expose] public section

open IsLocalRing Algebra

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : ValuationSubring K) : IsIntegrallyClosed V.toSubring := by
  rw [← V.integer_valuation]; infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : ValuationSubring K) : IsIntegrallyClosed V :=
  inferInstanceAs (IsIntegrallyClosed V.toSubring)

/-- Cast a valuation subring to a local subring. -/
/-
**ValuationSubring.toLocalSubring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K 
where toSubring
参数：A : ValuationSubring K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast a valuation subring to a local subring.
-/
def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  isLocalRing := A.isLocalRing
/-
**ValuationSubring.toLocalSubring_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ValuationSubring.toLocalSubring_injective : Function.Injective (ValuationS
ubring.toLocalSubring (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.toSubring_injective`：toSubring_injective : Function.Inj
ective (toSubring : ValuationSubring K -> Subring K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) :=
  fun _ _ h ↦ ValuationSubring.toSubring_injective congr(($h).toSubring)
/-
**LocalSubring.map_maximalIdeal_eq_top_of_isMax** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalSubring.map_maximalIdeal_eq_top_of_isMax {R : LocalSubring K} (hR : I
sMax R) {S : Subring K} (hS : R.toSubring < S) : (maximalIdeal R.toSubring).map 
(Subring.inclusion hS.le) = ⊤
参数：hR : IsMax R；hS : R.toSubring < S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LocalSubring.isLocalRing`：∀ {R : Type u_1} [inst : CommRing R] (self : L
ocalSubring R), IsLocalRing ↥self.toSubring
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LocalSubring.le_ofPrime`：le_ofPrime : A <= (ofPrime A P).toSubring
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `LocalSubring.instAtPrimeSubtypeMemSubringToSubringOfPrime`：∀ {K : Type u
_3} [inst : Field K] (A : Subring K) (P : Ideal ↥A) [inst_1 : P.IsPrime],   IsLo
calization.AtPrime (↥(LocalSubring.ofPrime A P)…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `IsMax.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → a = b
-/
lemma LocalSubring.map_maximalIdeal_eq_top_of_isMax {R : LocalSubring K}
    (hR : IsMax R) {S : Subring K} (hS : R.toSubring < S) :
    (maximalIdeal R.toSubring).map (Subring.inclusion hS.le) = ⊤ := by
  set mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R ≤ fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
    refine .trans ?_ (Ideal.map_mono h_incl)
    rw [Ideal.map_map]; rfl
  exact (hR.eq_of_le h_RleSₘ ▸ hS).not_ge (LocalSubring.le_ofPrime ..)

@[stacks 00IC]
-- the conclusion could be `IsIntegrallyClosedIn R.toSubring K`, which has slightly worse defeq.
/-
**LocalSubring.mem_of_isMax_of_isIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalSubring.mem_of_isMax_of_isIntegral {R : LocalSubring K} (hR : IsMax R
) {x : K} (hx : IsIntegral R.toSubring x) : x in R.toSubring
参数：hR : IsMax R；hx : IsIntegral R.toSubring x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Algebra.IsIntegral.adjoin`：Algebra.IsIntegral.adjoin {S : Set A} (hS : f
orall x in S, IsIntegral R x) : Algebra.IsIntegral R (adjoin R S)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LocalSubring.isLocalRing`：∀ {R : Type u_1} [inst : CommRing R] (self : L
ocalSubring R), IsLocalRing ↥self.toSubring
· 使用定理 `Ideal.exists_ideal_over_maximal_of_isIntegral`：exists_ideal_over_maximal
_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [P_max : IsMaximal P] (hP 
: RingHom.ker (algebraMap R S) <= P…
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FaithfulSMul.ker_algebraMap_eq_bot`：FaithfulSMul.ker_algebraMap_eq_bot (
R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A] : Ri
ngHom.ker (algebraMap R …
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `Subsemiring.instFaithfulSMulSubtypeMem`：∀ {M' : Type u_5} {α : Type u_6}
 [inst : SMul M' α] {S' : Type u_7} [inst_1 : SetLike S' M'] (s : S')   [Faithfu
lSMul M' α], FaithfulSMul (↥…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
（共 46 条，此处仅展示前 30 条）
-/
lemma LocalSubring.mem_of_isMax_of_isIntegral {R : LocalSubring K}
    (hR : IsMax R) {x : K} (hx : IsIntegral R.toSubring x) : x ∈ R.toSubring := by
  let S := R.toSubring[x]
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := S) (maximalIdeal R.toSubring) (le_maximalIdeal (by simp))
  have : R = .ofPrime S.toSubring Q := by
    have hRS : R.toSubring ≤ S.toSubring := fun r hr ↦ algebraMap_mem S ⟨r, hr⟩
    refine hR.eq_of_le ⟨hRS.trans (LocalSubring.le_ofPrime _ _), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
    refine .trans ?_ (Ideal.map_mono <| Ideal.map_le_iff_le_comap.mpr e.ge)
    rw [Ideal.map_map]; rfl
  rw [this]
  exact LocalSubring.le_ofPrime _ _ (self_mem_adjoin_singleton _ _)

@[stacks 052K]
/-
**ValuationSubring.isMax_toLocalSubring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ValuationSubring.isMax_toLocalSubring (R : ValuationSubring K) : IsMax R.t
oLocalSubring
参数：R : ValuationSubring K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `LocalSubring.toSubring_injective`：toSubring_injective : Function.Injecti
ve (toSubring (R
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ValuationSubring.mem_or_inv_mem'`：∀ {K : Type u} [inst : Field K] (self 
: ValuationSubring K) (x : K), x ∈ self.carrier ∨ x⁻¹ ∈ self.carrier
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ValuationSubring.zero_mem`：zero_mem : (0 : K) in A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `SubmonoidClass.instIsDedekindFiniteMonoidSubtypeMem`：∀ {M : Type u_1} {A
 : Type u_3} [inst : MulOneClass M] [inst_1 : SetLike A M] [hA : SubmonoidClass 
A M] (S : A)   [IsDedekindFiniteMonoid M]…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `inv_mul_eq_iff_eq_mul₀`：inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b =
 c ↔ b = a * c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma ValuationSubring.isMax_toLocalSubring (R : ValuationSubring K) :
    IsMax R.toLocalSubring := by
  intro S hS
  refine (LocalSubring.toSubring_injective (hS.1.antisymm fun x hx ↦ (R.2 x).elim id fun h ↦ ?_)).ge
  by_contra h'
  have hx0 : x ≠ 0 := by rintro rfl; exact h' R.zero_mem
  have : IsUnit (Subring.inclusion hS.1 ⟨x⁻¹, h⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨x', hx'⟩ := isUnit_iff_exists_inv.mp (hS.2.1 _ this)
  have : x' = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hx'
  exact h' (this ▸ x'.2)

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 00IB]
/-
**LocalSubring.exists_valuationRing_of_isMax** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalSubring.exists_valuationRing_of_isMax {R : LocalSubring K} (hR : IsMa
x R) : exists R' : ValuationSubring K, R'.toLocalSubring = R
参数：hR : IsMax R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocalSubring.mem_of_isMax_of_isIntegral`：LocalSubring.mem_of_isMax_of_is
Integral {R : LocalSubring K} (hR : IsMax R) {x : K} (hx : IsIntegral R.toSubrin
g x) : x in R.toSubring
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `LocalSubring.isLocalRing`：∀ {R : Type u_1} [inst : CommRing R] (self : L
ocalSubring R), IsLocalRing ↥self.toSubring
· 使用引理 `Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top`：e
xists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R] [CommR
ing S] [Algebra R S] (x : S) (I : Ideal R) (hI : I != ⊤) [I…
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `LocalSubring.map_maximalIdeal_eq_top_of_isMax`：LocalSubring.map_maximalI
deal_eq_top_of_isMax {R : LocalSubring K} (hR : IsMax R) {S : Subring K} (hS : R
.toSubring < S) : (maximalIdeal R.t…
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 56 条，此处仅展示前 30 条）
-/
lemma LocalSubring.exists_valuationRing_of_isMax {R : LocalSubring K} (hR : IsMax R) :
    ∃ R' : ValuationSubring K, R'.toLocalSubring = R := by
  suffices ∀ x ∉ R.toSubring, x⁻¹ ∈ R.toSubring from
    ⟨⟨R.toSubring, fun x ↦ or_iff_not_imp_left.mpr (this x)⟩, rfl⟩
  refine fun x hx ↦ mem_of_isMax_of_isIntegral hR ?_
  have hx0 : x ≠ 0 := fun e ↦ hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  let S := R.toSubring[x]
  have : R.toSubring < S.toSubring := SetLike.lt_iff_le_and_exists.mpr
    ⟨fun r hr ↦ algebraMap_mem S ⟨r, hr⟩, ⟨x, self_mem_adjoin_singleton _ _, hx⟩⟩
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal R.toSubring).ne_top
    (top_unique <| (map_maximalIdeal_eq_top_of_isMax hR this).ge.trans le_self_add)
  have H : IsUnit p.leadingCoeff := of_not_not fun h ↦ by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

/-- A local subring is maximal with respect to the domination order
  if and only if it is a valuation ring. -/
/-
**LocalSubring.isMax_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalSubring.isMax_iff {A : LocalSubring K} : IsMax A ↔ exists B : Valuati
onSubring K, B.toLocalSubring = A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocalSubring.exists_valuationRing_of_isMax`：LocalSubring.exists_valuatio
nRing_of_isMax {R : LocalSubring K} (hR : IsMax R) : exists R' : ValuationSubrin
g K, R'.toLocalSubring = R
· 使用引理 `ValuationSubring.isMax_toLocalSubring`：ValuationSubring.isMax_toLocalSub
ring (R : ValuationSubring K) : IsMax R.toLocalSubring

--- 原说明 ---
A local subring is maximal with respect to the domination order
  if and only if it is a valuation ring.
-/
lemma LocalSubring.isMax_iff {A : LocalSubring K} :
    IsMax A ↔ ∃ B : ValuationSubring K, B.toLocalSubring = A :=
  ⟨exists_valuationRing_of_isMax, fun ⟨B, e⟩ ↦ e ▸ B.isMax_toLocalSubring⟩

@[stacks 00IA]
/-
**LocalSubring.exists_le_valuationSubring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalSubring.exists_le_valuationSubring (A : LocalSubring K) : exists B : 
ValuationSubring K, A <= B.toLocalSubring
参数：A : LocalSubring K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty_Ici₀`：zorn_le_nonempty_Ici₀ (a : α) (ih : forall c subs
eteq Ici a, IsChain (· <= ·) c -> forall y in c, exists ub, forall z in c, z <= 
ub) (x : α)…
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用引理 `LocalSubring.toSubring_mono`：toSubring_mono : Monotone (toSubring (R
· 使用定理 `IsChain.directed`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [St
d.Refl r] {f : β → α} {c : Set β},   IsChain (f ⁻¹'o r) c → Directed r fun x => 
f ↑x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempty ι]
 {S : ι -> Subring R} (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exi
sts i, x in S i
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_add_one`：∀ {R : Type u_1} {inst : Semiri
ng R} [self : IsLocalRing R] {a b : R}, a + b = 1 → IsUnit a ∨ IsUnit b
· 使用定理 `LocalSubring.isLocalRing`：∀ {R : Type u_1} [inst : CommRing R] (self : L
ocalSubring R), IsLocalRing ↥self.toSubring
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `SubmonoidClass.instIsDedekindFiniteMonoidSubtypeMem`：∀ {M : Type u_1} {A
 : Type u_3} [inst : MulOneClass M] [inst_1 : SetLike A M] [hA : SubmonoidClass 
A M] (S : A)   [IsDedekindFiniteMonoid M]…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `LocalSubring.exists_valuationRing_of_isMax`：LocalSubring.exists_valuatio
nRing_of_isMax {R : LocalSubring K} (hR : IsMax R) : exists R' : ValuationSubrin
g K, R'.toLocalSubring = R
-/
lemma LocalSubring.exists_le_valuationSubring (A : LocalSubring K) :
    ∃ B : ValuationSubring K, A ≤ B.toLocalSubring := by
  suffices ∃ B, A ≤ B ∧ IsMax B by
    obtain ⟨B, hB, hB'⟩ := this
    obtain ⟨B, rfl⟩ := B.exists_valuationRing_of_isMax hB'
    exact ⟨B, hB⟩
  refine zorn_le_nonempty_Ici₀ _ ?_ _ le_rfl
  intro s hs H y hys
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
  · intro A hA
    refine ⟨le_iSup (fun i : s ↦ i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩
/-
**Ideal.image_subset_nonunits_valuationSubring** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.image_subset_nonunits_valuationSubring {A : Subring K} (I : Ideal A)
 (hI : I != ⊤) : exists B : ValuationSubring K, A <= B.toSubring ∧ A.subtype '' 
I subseteq B.nonunits
参数：I : Ideal A；hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用引理 `LocalSubring.exists_le_valuationSubring`：LocalSubring.exists_le_valuatio
nSubring (A : LocalSubring K) : exists B : ValuationSubring K, A <= B.toLocalSub
ring
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LocalSubring.le_ofPrime`：le_ofPrime : A <= (ofPrime A P).toSubring
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValuationSubring.image_maximalIdeal`：image_maximalIdeal : ((↑) : A -> K)
 '' IsLocalRing.maximalIdeal A = A.nonunits
· 使用定理 `LocalSubring.isLocalRing`：∀ {R : Type u_1} [inst : CommRing R] (self : L
ocalSubring R), IsLocalRing ↥self.toSubring
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `LocalSubring.instAtPrimeSubtypeMemSubringToSubringOfPrime`：∀ {K : Type u
_3} [inst : Field K] (A : Subring K) (P : Ideal ↥A) [inst_1 : P.IsPrime],   IsLo
calization.AtPrime (↥(LocalSubring.ofPrime A P)…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
-/
lemma Ideal.image_subset_nonunits_valuationSubring {A : Subring K} (I : Ideal A) (hI : I ≠ ⊤) :
    ∃ B : ValuationSubring K, A ≤ B.toSubring ∧ A.subtype '' I ⊆ B.nonunits := by
  have ⟨M, hM, le⟩ := I.exists_le_maximal hI
  have ⟨V, hV⟩ := (LocalSubring.ofPrime A M).exists_le_valuationSubring
  refine ⟨V, (LocalSubring.le_ofPrime ..).trans hV.1, ?_⟩
  rw [← V.image_maximalIdeal]
  refine .trans ?_ (Set.image_mono <| ((local_hom_TFAE _).out 0 2).mp hV.2)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M, map_map]
  refine .trans ?_ (Set.image_mono <| map_mono le)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨_, mem_map_of_mem _ ha, rfl⟩

open Polynomial Algebra in
/-
**Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn** 是 Mathlib 中的一个定理，
位于命名空间 `Subring`。
形式化陈述：∀ {K : Type u_3} [inst : Field K] {x : K} {R : Subring K},   x ∉ R → ∀ [Is
IntegrallyClosedIn (↥R) K], ∃ V, R ≤ V.toSubring ∧ x ∉ V
参数：↥R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Subring.zero_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R)
, 0 ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用引理 `Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top`：e
xists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R] [CommR
ing S] [Algebra R S] (x : S) (I : Ideal R) (hI : I != ⊤) [I…
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.isIntegrallyClosedIn_iff`：∀ {A : Type u_2} [inst : CommRing A] {
C : Type u_5} [inst_1 : SetLike C A] [inst_2 : SubringClass C A] {S : C},   IsIn
tegrallyClosedIn (↥S) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Ideal.image_subset_nonunits_valuationSubring`：Ideal.image_subset_nonunit
s_valuationSubring {A : Subring K} (I : Ideal A) (hI : I != ⊤) : exists B : Valu
ationSubring K, A <= B.toSubring ∧…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `ValuationSubring.inv_mem_nonunits_iff`：inv_mem_nonunits_iff {x : K} : x⁻
¹ in A.nonunits ↔ x = 0 ∨ x ∉ A
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
@[stacks 090P "part (1)"] lemma Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    {x : K} {R : Subring K} (hxR : x ∉ R) [IsIntegrallyClosedIn R K] :
    ∃ V : ValuationSubring K, R ≤ V.toSubring ∧ x ∉ V := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
  have : Ideal.span {xinv} ≠ ⊤ := fun eq ↦ hxR <|
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _
      (⊥ : Ideal R) bot_ne_top (top_unique <| eq.ge.trans le_add_self)
    (Subring.isIntegrallyClosedIn_iff).mp ‹_› ⟨p, by simpa [Monic, sub_eq_zero] using hp, hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ this
  exact ⟨V, fun r hr ↦ hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    (V.inv_mem_nonunits_iff.mp <| hV.2 ⟨_, Ideal.subset_span rfl, rfl⟩).resolve_left hx0⟩

set_option backward.isDefEq.respectTransparency.types false in
open Polynomial Algebra in
/-
**LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn** 是 Mathlib 中的
一个定理，位于命名空间 `LocalSubring`。
形式化陈述：∀ {K : Type u_3} [inst : Field K] {x : K} {R : LocalSubring K},   x ∉ R.to
Subring → ∀ [IsIntegrallyClosedIn (↥R.toSubring) K], ∃ V, R ≤ V.toLocalSubring ∧
 x ∉ V
参数：↥R.toSubring。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Subring.zero_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R)
, 0 ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `LocalSubring.isLocalRing`：∀ {R : Type u_1} [inst : CommRing R] (self : L
ocalSubring R), IsLocalRing ↥self.toSubring
· 使用引理 `Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top`：e
xists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top [CommRing R] [CommR
ing S] [Algebra R S] (x : S) (I : Ideal R) (hI : I != ⊤) [I…
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.isIntegrallyClosedIn_iff`：∀ {A : Type u_2} [inst : CommRing A] {
C : Type u_5} [inst_1 : SetLike C A] [inst_2 : SubringClass C A] {S : C},   IsIn
tegrallyClosedIn (↥S) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Subring.instNoZeroDivisorsSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocR
ing R] [NoZeroDivisors R] (s : Subring R), NoZeroDivisors ↥s
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `map_units_inv`：∀ {M : Type u} [inst : Monoid M] {α : Type u_1} [inst_1 :
 DivisionMonoid α] {F : Type u_2} [inst_2 : FunLike F M α]   [MonoidHomClass F M
 α]…
（共 55 条，此处仅展示前 30 条）
-/
@[stacks 090P "part (2)"] lemma LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    {x : K} {R : LocalSubring K} (hxR : x ∉ R.toSubring) [IsIntegrallyClosedIn R.toSubring K] :
    ∃ V : ValuationSubring K, R ≤ V.toLocalSubring ∧ x ∉ V := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.toSubring.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R.toSubring[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
  have : (maximalIdeal R.toSubring).map (algebraMap _ B) + .span {xinv} ≠ ⊤ := fun eq ↦ hxR <|
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _ _
      (maximalIdeal.isMaximal R.toSubring).ne_top eq
    have H : IsUnit p.leadingCoeff := of_not_not fun h ↦ by simpa using sub_mem h hp
    (Subring.isIntegrallyClosedIn_iff).mp ‹_›
      ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ this
  refine ⟨V, ⟨fun r hr ↦ hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    ((local_hom_TFAE _).out 3 0).mp fun r hr ↦ ?_⟩, (V.inv_mem_nonunits_iff.mp <|
      hV.2 ⟨_, le_add_self (α := Ideal B) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0⟩
  rw [← V.image_maximalIdeal] at hV
  obtain ⟨⟨r, _⟩, hr, rfl⟩ := hV.2 ⟨_, le_self_add (α := Ideal B) (Ideal.mem_map_of_mem _ hr), rfl⟩
  exact hr

/-- A subring integrally closed in a field is the intersection of valuation subrings
containing it. -/
/-
**Subring.eq_iInf_of_isIntegrallyClosedIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subring.eq_iInf_of_isIntegrallyClosedIn {R : Subring K} [IsIntegrallyClose
dIn R K] : R = ⨅ V : {V : ValuationSubring K // R <= V.toSubring}, V.1.toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`：∀ {K : Type 
u_3} [inst : Field K] {x : K} {R : Subring K},   x ∉ R → ∀ [IsIntegrallyClosedIn
 (↥R) K], ∃ V, R ≤ V.toSubring ∧ x ∉ V
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A subring integrally closed in a field is the intersection of valuation subrings
containing it.
-/
lemma Subring.eq_iInf_of_isIntegrallyClosedIn {R : Subring K} [IsIntegrallyClosedIn R K] :
    R = ⨅ V : {V : ValuationSubring K // R ≤ V.toSubring}, V.1.toSubring :=
  le_antisymm (le_iInf fun V ↦ V.2) fun _ h ↦ of_not_not fun hxR ↦
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

/-- A local subring integrally closed in a field is the intersection of valuation subrings
dominating it. -/
/-
**LocalSubring.eq_iInf_of_isIntegrallyClosedIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalSubring.eq_iInf_of_isIntegrallyClosedIn {R : LocalSubring K} [IsInteg
rallyClosedIn R.toSubring K] : R.toSubring = ⨅ V : {V : ValuationSubring K // R 
<= V.toLocalSubring}, V.1.toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn`：∀ {K : 
Type u_3} [inst : Field K] {x : K} {R : LocalSubring K},   x ∉ R.toSubring → ∀ [
IsIntegrallyClosedIn (↥R.toSubring) K], ∃ V, R ≤ V.to…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A local subring integrally closed in a field is the intersection of valuation su
brings
dominating it.
-/
lemma LocalSubring.eq_iInf_of_isIntegrallyClosedIn {R : LocalSubring K}
    [IsIntegrallyClosedIn R.toSubring K] :
    R.toSubring = ⨅ V : {V : ValuationSubring K // R ≤ V.toLocalSubring}, V.1.toSubring :=
  le_antisymm (le_iInf fun V ↦ V.2.1) fun _ h ↦ of_not_not fun hxR ↦
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

/-- The integral closure of a subset in a field is the intersection of all valuation subrings
containing it. -/
/-
**iInf_valuationSubring_superset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iInf_valuationSubring_superset {s : Set K} : (⨅ V : {V : ValuationSubring 
K // s subseteq V.toSubring}, V.1.toSubring) = (integralClosure (Subring.closure
 s) K).toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subring.integralClosure_subring_le_iff`：integralClosure_subring_le_iff {
T : Subring A} [IsIntegrallyClosedIn T A] : (integralClosure S A).toSubring <= T
 ↔ .ofClass S <= T
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用引理 `Subring.eq_iInf_of_isIntegrallyClosedIn`：Subring.eq_iInf_of_isIntegrally
ClosedIn {R : Subring K} [IsIntegrallyClosedIn R K] : R = ⨅ V : {V : ValuationSu
bring K // R <= V.toSubring},…
· 使用定理 `instIsIntegrallyClosedInSubtypeMemSubringToSubringIntegralClosure`：∀ {R 
: Type u_1} [inst : CommRing R] {A : Type u_2} [inst_1 : CommRing A] [inst_2 : A
lgebra R A],   IsIntegrallyClosedIn (↥(integralClosure …

--- 原说明 ---
The integral closure of a subset in a field is the intersection of all valuation
 subrings
containing it.
-/
lemma iInf_valuationSubring_superset {s : Set K} :
    (⨅ V : {V : ValuationSubring K // s ⊆ V.toSubring}, V.1.toSubring) =
    (integralClosure (Subring.closure s) K).toSubring := by
  refine .trans ?_ Subring.eq_iInf_of_isIntegrallyClosedIn.symm
  simp_rw [iInf_subtype]
  congr! with V
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  rw [Subring.integralClosure_subring_le_iff]
  exact Subring.closure_le.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**bijective_rangeRestrict_comp_of_valuationRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bijective_rangeRestrict_comp_of_valuationRing [IsDomain R] [ValuationRing 
R] [IsLocalRing S] [Algebra R K] [IsFractionRing R K] (f : R ->+* S) (g : S ->+*
 K) (h : g.comp f = algebraMap R K) [IsLocalHom f] : Function.Bijective (g.range
Restrict.comp f)
参数：f : R ->+* S；g : S ->+* K；h : g.comp f = algebraMap R K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `ValuationRing.isInteger_or_isInteger`：isInteger_or_isInteger [h : Valuat
ionRing R] (x : K) : IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x
⁻¹
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用引理 `ValuationSubring.isMax_toLocalSubring`：ValuationSubring.isMax_toLocalSub
ring (R : ValuationSubring K) : IsMax R.toLocalSubring
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.of_map`：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit 
(f a)) : IsUnit a
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
· 使用定理 `IsLocalHom.of_surjective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] [Nontrivial S] [IsLocalRing R] (f : R →+* S),   Func
tion.Surjectiv…
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `RingHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : R ->+* S
) : Function.Surjective f.rangeRestrict
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma bijective_rangeRestrict_comp_of_valuationRing [IsDomain R] [ValuationRing R]
    [IsLocalRing S] [Algebra R K] [IsFractionRing R K]
    (f : R →+* S) (g : S →+* K) (h : g.comp f = algebraMap R K) [IsLocalHom f] :
    Function.Bijective (g.rangeRestrict.comp f) := by
  refine ⟨?_, ?_⟩
  · exact .of_comp (f := Subtype.val) (by convert! (IsFractionRing.injective R K); rw [← h]; rfl)
  · let V : ValuationSubring K :=
      ⟨(algebraMap R K).range, ValuationRing.isInteger_or_isInteger R⟩
    suffices LocalSubring.range g ≤ V.toLocalSubring by
      rintro ⟨_, x, rfl⟩
      obtain ⟨y, hy⟩ := this.1 ⟨x, rfl⟩
      exact ⟨y, Subtype.ext (by simpa [← h] using hy)⟩
    apply V.isMax_toLocalSubring
    have H : (algebraMap R K).range ≤ g.range := fun x ⟨a, ha⟩ ↦ ⟨f a, by simp [← ha, ← h]⟩
    refine ⟨H, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ (ha : IsUnit (M := g.range) ⟨algebraMap R K a, _⟩)
    suffices IsUnit a from this.map (algebraMap R K).rangeRestrict
    apply IsUnit.of_map f
    apply (IsLocalHom.of_surjective g.rangeRestrict g.rangeRestrict_surjective).1
    convert! ha
    simp [← h]
/-
**IsLocalRing.exists_factor_valuationRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalRing.exists_factor_valuationRing [IsLocalRing R] (f : R ->+* K) : e
xists (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h)
参数：f : R ->+* K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `LocalSubring.exists_le_valuationSubring`：LocalSubring.exists_le_valuatio
nSubring (A : LocalSubring K) : exists B : ValuationSubring K, A <= B.toLocalSub
ring
· 使用定理 `RingHom.isLocalHom_comp`：RingHom.isLocalHom_comp (g : S ->+* T) (f : R -
>+* S) [IsLocalHom g] [IsLocalHom f] : IsLocalHom (g.comp f) where map_nonunit a
· 使用定理 `IsLocalHom.of_surjective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] [Nontrivial S] [IsLocalRing R] (f : R →+* S),   Func
tion.Surjectiv…
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `RingHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : R ->+* S
) : Function.Surjective f.rangeRestrict
-/
lemma IsLocalRing.exists_factor_valuationRing [IsLocalRing R] (f : R →+* K) :
    ∃ (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h) := by
  obtain ⟨B, hB⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨B, fun x ↦ hB.1 ⟨x, rfl⟩, ?_⟩
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hB.2 (.of_surjective _ f.rangeRestrict_surjective)
