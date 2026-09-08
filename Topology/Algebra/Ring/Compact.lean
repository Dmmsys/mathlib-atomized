/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!

# Compact Hausdorff Rings

## Main results
- `IsArtinianRing.finite_of_compactSpace_of_t2Space`:
  Compact Hausdorff Artinian rings are finite (and thus discrete).
- `Ideal.isOpen_of_isMaximal`:
  Maximal ideals are open in compact Hausdorff Noetherian rings.
- `IsLocalRing.isOpen_iff_finite_quotient`:
  An ideal in a compact Hausdorff Noetherian local ring is open iff it has finite index.
- `IsDedekindDomain.isOpen_iff`:
  An ideal in a compact Hausdorff Dedekind domain (that is not a field) is open iff it is non-zero.

## Future projects
Show that compact Hausdorff rings are totally disconnected and linearly topologized.
See https://ncatlab.org/nlab/show/compact+Hausdorff+rings+are+profinite

-/

public section

attribute [local instance] Ideal.Quotient.field Fintype.ofFinite finite_of_compact_of_discrete
  DivisionRing.finite_of_compactSpace_of_t2Space

variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R] [CompactSpace R] [T2Space R]

namespace IsArtinianRing

/-- Compact Hausdorff Artinian (commutative) rings are finite. This is not an instance, as it would
apply to every `Finite` goal, causing slowly failing typeclass search in some cases. -/
/-
**IsArtinianRing.finite_of_compactSpace_of_t2Space** 是 Mathlib 中的一个定理，位于命名空间 `Is
ArtinianRing`。
形式化陈述：finite_of_compactSpace_of_t2Space [IsArtinianRing R] : Finite R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.isNilpotent_jacobson_bot`：isNilpotent_jacobson_bot {R} [R
ing R] [IsArtinianRing R] : IsNilpotent (Ideal.jacobson (⊥ : Ideal R))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsArtinianRing.instFinitePrimeSpectrum`：∀ (R : Type u_1) [inst : CommRin
g R] [IsArtinianRing R], Finite (PrimeSpectrum R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.instIsOrderedRing`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A],   IsOrderedRing (Submodul
e R A)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `Ideal.jacobson_bot`：jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobso
n R
· 使用定理 `Ring.jacobson_eq_sInf_isMaximal`：jacobson_eq_sInf_isMaximal : jacobson R
 = sInf {I : Ideal R | I.IsMaximal}
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.prod_le_inf`：prod_le_inf {s : Finset ι} {f : ι -> Ideal R} : s.pro
d f <= s.inf f
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Ideal.finite_quotient_prod`：Ideal.finite_quotient_prod {ι : Type*} (I : 
ι -> Ideal R) (s : Finset ι) (hI : forall i in s, (I i).FG) (hI' : forall i in s
, Finite (R ⧸ I …
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `DivisionRing.finite_of_compactSpace_of_t2Space`：DivisionRing.finite_of_c
ompactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K] [IsTopologicalR
ing K] [CompactSpace K] [T2Space K] …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `instCompactSpaceQuotientIdeal`：∀ {R : Type u_1} [inst : TopologicalSpace
 R] [inst_1 : CommRing R] (N : Ideal R) [CompactSpace R], CompactSpace (R ⧸ N)
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Compact Hausdorff Artinian (commutative) rings are finite. This is not an instan
ce, as it would
apply to every `Finite` goal, causing slowly failing typeclass search in some ca
ses.
-/
theorem finite_of_compactSpace_of_t2Space [IsArtinianRing R] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    gcongr
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal, le_sInf_iff]
    exact fun I hI ↦ Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ ↦ IsNoetherian.noetherian _) (fun _ _ ↦ inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

end IsArtinianRing

section IsNoetherianRing

variable [IsNoetherianRing R]

/-
**Ideal.isOpen_of_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isOpen_of_isMaximal (I : Ideal R) [I.IsMaximal] : IsOpen (X
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.finiteIndex_of_finite_quotient`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [Finite (G ⧸ H)], H.FiniteIndex
· 使用定理 `AddSubgroup.isOpen_of_isClosed_of_finiteIndex`：∀ {G : Type u} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (H : AddSubg
roup G)   [H.FiniteIndex], IsClosed…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
lemma Ideal.isOpen_of_isMaximal (I : Ideal R) [I.IsMaximal] : IsOpen (X := R) I :=
  have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))
/-
**Ideal.isOpen_pow_of_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isOpen_pow_of_isMaximal (I : Ideal R) [I.IsMaximal] (n : Nat) : IsOp
en (X
参数：I : Ideal R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddSubgroup.finiteIndex_of_finite_quotient`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [Finite (G ⧸ H)], H.FiniteIndex
· 使用引理 `Ideal.finite_quotient_pow`：Ideal.finite_quotient_pow (hI : I.FG) [Finite
 (R ⧸ I)] (n) : Finite (R ⧸ I ^ n)
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `DivisionRing.finite_of_compactSpace_of_t2Space`：DivisionRing.finite_of_c
ompactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K] [IsTopologicalR
ing K] [CompactSpace K] [T2Space K] …
· 使用定理 `instCompactSpaceQuotientIdeal`：∀ {R : Type u_1} [inst : TopologicalSpace
 R] [inst_1 : CommRing R] (N : Ideal R) [CompactSpace R], CompactSpace (R ⧸ N)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsNoetherianRing.isClosed_ideal`：∀ {R : Type u_3} [inst : CommRing R] [i
nst_1 : TopologicalSpace R] [IsTopologicalRing R] [IsNoetherianRing R]   [Compac
tSpace R] [T2Space R]…
· 使用定理 `AddSubgroup.isOpen_of_isClosed_of_finiteIndex`：∀ {G : Type u} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (H : AddSubg
roup G)   [H.FiniteIndex], IsClosed…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用引理 `Ideal.isCompact_of_fg`：Ideal.isCompact_of_fg [IsTopologicalSemiring R] [
CompactSpace R] {I : Ideal R} (hI : I.FG) : IsCompact (X
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
lemma Ideal.isOpen_pow_of_isMaximal (I : Ideal R) [I.IsMaximal] (n : ℕ) :
    IsOpen (X := R) ↑(I ^ n) :=
  have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed

-- Note: this is only by infer_instance because of the opened local instances.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := inferInstance

end IsNoetherianRing

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/-
**IsLocalRing.isOpen_maximalIdeal_pow** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：isOpen_maximalIdeal_pow (n : Nat) : IsOpen (X
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.isOpen_pow_of_isMaximal`：Ideal.isOpen_pow_of_isMaximal (I : Ideal 
R) [I.IsMaximal] (n : Nat) : IsOpen (X
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
lemma isOpen_maximalIdeal_pow (n : ℕ) :
    IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  Ideal.isOpen_pow_of_isMaximal _ _

variable (R) in
/-
**IsLocalRing.isOpen_maximalIdeal** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：isOpen_maximalIdeal : IsOpen (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.isOpen_of_isMaximal`：Ideal.isOpen_of_isMaximal (I : Ideal R) [I.Is
Maximal] : IsOpen (X
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
lemma isOpen_maximalIdeal : IsOpen (X := R) ↑(maximalIdeal R) :=
  Ideal.isOpen_of_isMaximal _
/-
**IsLocalRing.finite_residueField_of_compactSpace** 是 Mathlib 中的一个实例，位于命名空间 `IsL
ocalRing`。
形式化陈述：finite_residueField_of_compactSpace : Finite (ResidueField R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finite_residueField_of_compactSpace : Finite (ResidueField R) :=
  inferInstanceAs (Finite (R ⧸ _))
/-
**IsLocalRing.isOpen_iff_finite_quotient** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`
。
形式化陈述：isOpen_iff_finite_quotient {I : Ideal R} : IsOpen (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.quotient_finite_of_isOpen`：∀ {G : Type u_1} [inst : AddGroup
 G] [inst_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] [CompactSpace G]  
 (U : AddSubgroup G), IsOpe…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`：exist
s_maximalIdeal_pow_le_of_isArtinianRing_quotient (I : Ideal R) [IsArtinianRing (
R ⧸ I)] : exists n, maximalIdeal R ^ n <= I
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AddSubgroup.isOpen_mono`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [SeparatelyContinuousAdd G] {H₁ H₂ : AddSubgroup G},   H₁ ≤ 
H₂ → IsOpen ↑…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalRing.isOpen_maximalIdeal_pow`：isOpen_maximalIdeal_pow (n : Nat) :
 IsOpen (X
-/
lemma isOpen_iff_finite_quotient {I : Ideal R} :
    IsOpen (X := R) I ↔ Finite (R ⧸ I) := by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

end IsLocalRing

section IsDedekindDomain

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsDedekindDomain.isOpen_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDedekindDomain.isOpen_of_ne_bot [IsDedekindDomain R] {I : Ideal R} (hI :
 I != ⊥) : IsOpen (X
参数：hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.finprod_heightOneSpectrum_factorization`：finprod_heightOneSpectrum
_factorization {I : Ideal R} (hI : I != 0) : ∏ᶠ v : HeightOneSpectrum R, v.maxPo
wDividing I = I
· 使用定理 `Ideal.hasFiniteMulSupport`：hasFiniteMulSupport {I : Ideal R} (hI : I != 
0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I
· 使用定理 `finprod_eq_finsetProd_of_mulSupport_subset`：finprod_eq_finsetProd_of_mul
Support_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq (s : Set α
)) : ∏ᶠ i, f i = ∏ i in s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `AddSubgroup.isOpen_of_isClosed_of_finiteIndex`：∀ {G : Type u} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [SeparatelyContinuousAdd G] (H : AddSubg
roup G)   [H.FiniteIndex], IsClosed…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `AddSubgroup.finiteIndex_of_finite_quotient`：∀ {G : Type u_1} [inst : Add
Group G] {H : AddSubgroup G} [Finite (G ⧸ H)], H.FiniteIndex
· 使用引理 `Ideal.finite_quotient_prod`：Ideal.finite_quotient_prod {ι : Type*} (I : 
ι -> Ideal R) (s : Finset ι) (hI : forall i in s, (I i).FG) (hI' : forall i in s
, Finite (R ⧸ I …
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用引理 `Ideal.finite_quotient_pow`：Ideal.finite_quotient_pow (hI : I.FG) [Finite
 (R ⧸ I)] (n) : Finite (R ⧸ I ^ n)
· 使用定理 `DivisionRing.finite_of_compactSpace_of_t2Space`：DivisionRing.finite_of_c
ompactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K] [IsTopologicalR
ing K] [CompactSpace K] [T2Space K] …
· 使用定理 `instCompactSpaceQuotientIdeal`：∀ {R : Type u_1} [inst : TopologicalSpace
 R] [inst_1 : CommRing R] (N : Ideal R) [CompactSpace R], CompactSpace (R ⧸ N)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsNoetherianRing.isClosed_ideal`：∀ {R : Type u_3} [inst : CommRing R] [i
nst_1 : TopologicalSpace R] [IsTopologicalRing R] [IsNoetherianRing R]   [Compac
tSpace R] [T2Space R]…
-/
lemma IsDedekindDomain.isOpen_of_ne_bot
    [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) :
    IsOpen (X := R) I := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI,
    finprod_eq_finsetProd_of_mulSupport_subset _
      (s := (Ideal.hasFiniteMulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ ↦ IsNoetherian.noetherian _) fun _ _ ↦ ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
/-
**IsDedekindDomain.isOpen_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDedekindDomain.isOpen_iff [IsDedekindDomain R] (hR : ¬ IsField R) {I : I
deal R} : IsOpen (X
参数：hR : ¬ IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton_zero`：∀ {G : Type w} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G],   DiscreteTopo
logy G ↔ IsOpen {0}
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Finite.isField_of_domain`：Finite.isField_of_domain (R) [CommRing R] [IsD
omain R] [Finite R] : IsField R
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `finite_of_compact_of_discrete`：finite_of_compact_of_discrete [CompactSpa
ce X] [DiscreteTopology X] : Finite X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsDedekindDomain.isOpen_of_ne_bot`：IsDedekindDomain.isOpen_of_ne_bot [Is
DedekindDomain R] {I : Ideal R} (hI : I != ⊥) : IsOpen (X
-/
lemma IsDedekindDomain.isOpen_iff
    [IsDedekindDomain R] (hR : ¬ IsField R) {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ := by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)
/-
**IsDiscreteValuationRing.isOpen_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscreteValuationRing.isOpen_iff [IsDomain R] [IsDiscreteValuationRing R
] {I : Ideal R} : IsOpen (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDedekindDomain.isOpen_iff`：IsDedekindDomain.isOpen_iff [IsDedekindDoma
in R] (hR : ¬ IsField R) {I : Ideal R} : IsOpen (X
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `IsDiscreteValuationRing.not_isField`：not_isField : ¬IsField R
-/
lemma IsDiscreteValuationRing.isOpen_iff
    [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ :=
  IsDedekindDomain.isOpen_iff (not_isField R)

end IsDedekindDomain

