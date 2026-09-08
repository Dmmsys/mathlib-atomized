/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.LinearIndependent.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.OreLocalization.OreSet

/-!
# Rank of localization

## Main statements

- `IsLocalizedModule.lift_rank_eq`: `rank_Rₚ Mₚ = rank R M`.
- `rank_quotient_add_rank_of_isDomain`: The **rank-nullity theorem** for commutative domains.
-/

public section

open Cardinal Module nonZeroDivisors

section CommRing

universe uR uS uT uM uN uP

variable {R : Type uR} (S : Type uS) {M : Type uM} {N : Type uN}
variable [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]
variable (hp : p ≤ R⁰)

section
include hp

section
include f

/-
**IsLocalizedModule.lift_rank_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.lift_rank_eq : Cardinal.lift.{uM} (Module.rank R N) = Ca
rdinal.lift.{uN} (Module.rank R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用引理 `IsLocalizedModule.linearIndependent_lift`：IsLocalizedModule.linearIndepe
ndent_lift {ι} {v : ι -> Mₛ} (hf : LinearIndependent R v) : exists w : ι -> M, L
inearIndependent R w
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LinearIndependent.of_isLocalizedModule_of_isRegular`：LinearIndependent.o
f_isLocalizedModule_of_isRegular {ι : Type*} {v : ι -> M} (hv : LinearIndependen
t R v) (h : forall s : S, IsRegular (s : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_nonZeroDivisors_iff_isRegular`：le_nonZeroDivisors_iff_isRegular {S : 
Submonoid R} : S <= R⁰ ↔ forall s : S, IsRegular (s : R)
-/
lemma IsLocalizedModule.lift_rank_eq :
    Cardinal.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M) := by
  cases subsingleton_or_nontrivial R
  · simp only [rank_subsingleton, lift_one]
  apply le_antisymm <;>
    rw [Module.rank_def, lift_iSup bddAbove_of_small] <;>
    apply ciSup_le' <;>
    intro ⟨s, hs⟩
  exacts [(IsLocalizedModule.linearIndependent_lift p f hs).choose_spec.cardinal_lift_le_rank,
    hs.of_isLocalizedModule_of_isRegular p f (le_nonZeroDivisors_iff_isRegular.mp hp)
      |>.cardinal_lift_le_rank]
/-
**IsLocalizedModule.finrank_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.finrank_eq : finrank R N = finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `IsLocalizedModule.lift_rank_eq`：IsLocalizedModule.lift_rank_eq : Cardina
l.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M)
-/
lemma IsLocalizedModule.finrank_eq : finrank R N = finrank R M := by
  simpa using! congr_arg toNat (lift_rank_eq p f hp)

end

/-
**IsLocalizedModule.rank_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.rank_eq {N : Type uM} [AddCommGroup N] [Module R N] (f :
 M ->ₗ[R] N) [IsLocalizedModule p f] : Module.rank R N = Module.rank R M
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `IsLocalizedModule.lift_rank_eq`：IsLocalizedModule.lift_rank_eq : Cardina
l.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M)
-/
lemma IsLocalizedModule.rank_eq {N : Type uM} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    [IsLocalizedModule p f] : Module.rank R N = Module.rank R M := by
  simpa using lift_rank_eq p f hp
/-
**IsLocalization.rank_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.rank_eq : Module.rank S N = Module.rank R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `LinearIndependent.localization`：LinearIndependent.localization [Module R
ₛ M] [IsScalarTower R Rₛ M] {ι : Type*} {b : ι -> M} (hli : LinearIndependent R 
b) : LinearIndepende…
-/
lemma IsLocalization.rank_eq : Module.rank S N = Module.rank R N := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R S).codomain_trivial; simp only [rank_subsingleton]
  have inj := IsLocalization.injective S hp
  apply le_antisymm <;> (rw [Module.rank]; apply ciSup_le'; intro ⟨s, hs⟩)
  · have := (faithfulSMul_iff_algebraMap_injective R S).mpr inj
    exact (hs.restrict_scalars' R).cardinal_le_rank
  · have := inj.nontrivial
    exact (hs.localization S p).cardinal_le_rank
/-
**IsLocalization.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.finrank_eq : finrank S N = finrank R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalization.rank_eq`：IsLocalization.rank_eq : Module.rank S N = Modul
e.rank R N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLocalization.finrank_eq : finrank S N = finrank R N := by
  simp_rw [finrank, rank_eq S p hp]

end

variable {S} in
/-
**IsLocalization.linearIndepOn_finsetIntegerMultiple** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsLocalization.linearIndepOn_finsetIntegerMultiple {A : Type*} [CommRing A
] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (M : Submonoid S) [IsLocaliz
ation M A] [FaithfulSMul S A] {s : Finset A} (hs : LinearIndepOn R id (s : Set A
)) [DecidableEq S] : LinearIndepOn R id (finsetIntegerMultiple M s : Set S)
参数：M : Submonoid S；hs : LinearIndepOn R id (s : Set A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIndepOn.id_image_algebraMap_iff`：LinearIndepOn.id_image_algebraMap
_iff {s : Set S} : LinearIndepOn R id (algebraMap S A '' s) ↔ LinearIndepOn R id
 s
· 使用定理 `IsLocalization.finsetIntegerMultiple_image`：finsetIntegerMultiple_image 
[DecidableEq R] (s : Finset S) : algebraMap R S '' finsetIntegerMultiple M s = c
ommonDenomOfFinset M s • (s : Se…
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用引理 `linearIndepOn_finset_iff`：linearIndepOn_finset_iff {s : Finset ι} : Line
arIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f
 i = 0
· 使用定理 `Finset.smul_finset_def`：∀ {α : Type u_2} {β : Type u_3} [inst : Decidabl
eEq β] [inst_1 : SMul α β] {s : Finset β} {a : α},   a • s = Finset.image (fun x
 => a • x) s
· 使用引理 `Finset.forall_mem_image`：forall_mem_image {p : β -> Prop} : (forall y in
 s.image f, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `IsLocalization.smul_bijective`：smul_bijective (m : M) : Bijective fun s 
: S => m • s
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem IsLocalization.linearIndepOn_finsetIntegerMultiple {A : Type*} [CommRing A] [Algebra S A]
    [Algebra R A] [IsScalarTower R S A] (M : Submonoid S) [IsLocalization M A] [FaithfulSMul S A]
    {s : Finset A} (hs : LinearIndepOn R id (s : Set A)) [DecidableEq S] :
    LinearIndepOn R id (finsetIntegerMultiple M s : Set S) := by
  classical
  rw [← LinearIndepOn.id_image_algebraMap_iff (A := A),
    finsetIntegerMultiple_image, ← s.coe_smul_finset]
  rw [linearIndepOn_finset_iff] at hs ⊢
  intro f h
  rw [s.smul_finset_def, s.forall_mem_image]
  apply hs
  have inj := (IsLocalization.smul_bijective A (commonDenomOfFinset M s)).injective
  rw [← inj.eq_iff, smul_zero, s.smul_sum, ← h, s.smul_finset_def, s.sum_image inj.injOn]
  exact s.sum_congr rfl fun x hx ↦ smul_comm ..

section

variable (R N) [IsFractionRing R S]

/-- Given `IsScalarTower R S N`, if `S` is the fraction ring of `R`, then the rank `rank S N`
of the right part of the tower equals the rank `rank R N` of the whole tower.

See `IsFractionRing.finrank_right_eq` for the finrank version. -/
/-
**IsFractionRing.rank_right_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.rank_right_eq : Module.rank S N = Module.rank R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.rank_eq`：IsLocalization.rank_eq : Module.rank S N = Modul
e.rank R N
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Given `IsScalarTower R S N`, if `S` is the fraction ring of `R`, then the rank `
rank S N`
of the right part of the tower equals the rank `rank R N` of the whole tower.

See `IsFractionRing.finrank_right_eq` for the finrank version.
-/
theorem IsFractionRing.rank_right_eq : Module.rank S N = Module.rank R N :=
  IsLocalization.rank_eq S R⁰ le_rfl

/-- Given `IsScalarTower R S N`, if `S` is the fraction ring of `R`, then the finrank `finrank S N`
of the right part of the tower equals the finrank `finrank R N` of the whole tower.

See `IsFractionRing.rank_right_eq` for the rank version.
See `IsFractionRing.finrank_left_eq` for the left version.
See `IsFractionRing.finrank_eq` for the simultaneous version. -/
/-
**IsFractionRing.finrank_right_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.finrank_right_eq : finrank S N = finrank R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.finrank_eq`：IsLocalization.finrank_eq : finrank S N = fin
rank R N
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Given `IsScalarTower R S N`, if `S` is the fraction ring of `R`, then the finran
k `finrank S N`
of the right part of the tower equals the finrank `finrank R N` of the whole tow
er.

See `IsFractionRing.rank_right_eq` for the rank version.
See `IsFractionRing.finrank_left_eq` for the left version.
See `IsFractionRing.finrank_eq` for the simultaneous version.
-/
theorem IsFractionRing.finrank_right_eq : finrank S N = finrank R N :=
  IsLocalization.finrank_eq S R⁰ le_rfl

end

variable (R) in
open IsLocalization in
/-- Given `IsScalarTower R S A`, if `A` is the fraction ring of `S`, then the finrank `finrank R S`
of the left part of the tower equals the finrank `finrank R A` of the whole tower.

See `IsFractionRing.finrank_right_eq` for the right version.
See `IsFractionRing.finrank_eq` for the simultaneous version. -/
/-
**IsFractionRing.finrank_left_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFractionRing.finrank_left_eq (A : Type*) [CommRing A] [Algebra S A] [Alg
ebra R A] [IsScalarTower R S A] [IsFractionRing S A] : Module.finrank R S = Modu
le.finrank R A
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_subsingleton`：∀ {R : Type u} {M : Type v} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsingleton R],
 Module.finrank R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.toNat_eq_of_forall_le_iff`：toNat_eq_of_forall_le_iff {c : Cardi
nal.{u}} {d : Cardinal.{v}} (h : forall n : Nat, n <= c ↔ n <= d) : c.toNat = d.
toNat
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearIndependent.algebraMap_comp_iff`：LinearIndependent.algebraMap_comp
_iff {ι : Type*} {v : ι -> S} : LinearIndependent R (algebraMap S A ∘ v) ↔ Linea
rIndependent R v
· 使用定理 `IsLocalization.card_finsetIntegerMultiple`：card_finsetIntegerMultiple [D
ecidableEq R] (s : Finset S) : (finsetIntegerMultiple M s).card = s.card
· 使用定理 `IsLocalization.linearIndepOn_finsetIntegerMultiple`：IsLocalization.linea
rIndepOn_finsetIntegerMultiple {A : Type*} [CommRing A] [Algebra S A] [Algebra R
 A] [IsScalarTower R S A] (M : Submonoid…

--- 原说明 ---
Given `IsScalarTower R S A`, if `A` is the fraction ring of `S`, then the finran
k `finrank R S`
of the left part of the tower equals the finrank `finrank R A` of the whole towe
r.

See `IsFractionRing.finrank_right_eq` for the right version.
See `IsFractionRing.finrank_eq` for the simultaneous version.
-/
theorem IsFractionRing.finrank_left_eq (A : Type*) [CommRing A] [Algebra S A] [Algebra R A]
    [IsScalarTower R S A] [IsFractionRing S A] : Module.finrank R S = Module.finrank R A := by
  nontriviality R
  classical
  apply Cardinal.toNat_eq_of_forall_le_iff
  intro n
  simp_rw [Module.le_rank_iff_exists_finset, LinearIndepOn]
  constructor
  · rintro ⟨s, rfl, hs⟩
    let f : S ↪ A := ⟨algebraMap S A, FaithfulSMul.algebraMap_injective S A⟩
    exact ⟨s.map f, s.card_map f,
      (linearIndependent_equiv (s.equivMap f)).mp (LinearIndependent.algebraMap_comp_iff.mpr hs)⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨finsetIntegerMultiple S⁰ s, card_finsetIntegerMultiple S⁰ s,
      linearIndepOn_finsetIntegerMultiple S⁰ hs⟩

/-- If `K` is the fraction ring of `A` and `L` is the fraction ring of `B`, then the finrank
`finrank K L` of the fraction rings equals the finrank `finrank A B` of the base rings.

See `IsFractionRing.finrank_left_eq` and `IsFractionRing.finrank_right_eq` for one-sided versions.
See `Algebra.IsAlgebraic.rank_of_isFractionRing` for a rank version with additional assumptions. -/
/-
**IsFractionRing.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (A : Type u_1) (K : Type u_2) (B : Type u_3) (L : Type u_4) [inst : Comm
Ring A] [inst_1 : CommRing K]   [inst_2 : CommRing B] [inst_3 : CommRing L] [ins
t_4 : Algebra A B] [inst_5 : _root_.Module K L] [inst_6 : Algebra A K]   [inst_7
 : Algebra B L] [inst_8 : Algebra A L] [IsScalarTower A K L] [IsScalarTower A B 
L] [IsFractionRing A K]   [IsFractionRing B L], Module.finrank K L = Module.finr
ank A B
参数：A : Type u_1；K : Type u_2；B : Type u_3；L : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsFractionRing.finrank_right_eq`：IsFractionRing.finrank_right_eq : finra
nk S N = finrank R N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.finrank_left_eq`：IsFractionRing.finrank_left_eq (A : Type
*) [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [IsFractionRin
g S A] : Module.finr…

--- 原说明 ---
If `K` is the fraction ring of `A` and `L` is the fraction ring of `B`, then the
 finrank
`finrank K L` of the fraction rings equals the finrank `finrank A B` of the base
 rings.

See `IsFractionRing.finrank_left_eq` and `IsFractionRing.finrank_right_eq` for o
ne-sided versions.
See `Algebra.IsAlgebraic.rank_of_isFractionRing` for a rank version with additio
nal assumptions.
-/
protected theorem IsFractionRing.finrank_eq (A K B L : Type*)
    [CommRing A] [CommRing K] [CommRing B] [CommRing L] [Algebra A B] [Module K L]
    [Algebra A K] [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] : Module.finrank K L = Module.finrank A B :=
  (finrank_right_eq A K L).trans (finrank_left_eq A B L).symm

variable (R M) in
/-
**exists_set_linearIndependent_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_set_linearIndependent_of_isDomain [IsDomain R] : exists s : Set M, 
#s = Module.rank R M ∧ LinearIndepOn R id s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `IsLocalizedModule.linearIndependent_lift`：IsLocalizedModule.linearIndepe
ndent_lift {ι} {v : ι -> Mₛ} (hf : LinearIndependent R v) : exists w : ι -> M, L
inearIndependent R w
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `IsLocalization.rank_eq`：IsLocalization.rank_eq : Module.rank S N = Modul
e.rank R N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `IsLocalizedModule.lift_rank_eq`：IsLocalizedModule.lift_rank_eq : Cardina
l.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndepOn_id_range_iff`：linearIndepOn_id_range_iff {ι} {f : ι -> M} 
(hf : Injective f) : LinearIndepOn R id (range f) ↔ LinearIndependent R f
-/
theorem exists_set_linearIndependent_of_isDomain [IsDomain R] :
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndepOn R id s := by
  obtain ⟨w, hw⟩ :=
    IsLocalizedModule.linearIndependent_lift R⁰ (LocalizedModule.mkLinearMap R⁰ M) <|
      Module.Free.chooseBasis (FractionRing R) (LocalizedModule R⁰ M)
        |>.linearIndependent.restrict_scalars' _
  refine ⟨Set.range w, ?_, (linearIndepOn_id_range_iff hw.injective).mpr hw⟩
  apply Cardinal.lift_injective.{max uR uM}
  rw [Cardinal.mk_range_eq_of_injective hw.injective, ← Module.Free.rank_eq_card_chooseBasisIndex,
    IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl]

/-- The **rank-nullity theorem** for commutative domains. Also see `rank_quotient_add_rank`. -/
/-
**rank_quotient_add_rank_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) : Mod
ule.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M
参数：M' : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalizedModule.lift_rank_eq`：IsLocalizedModule.lift_rank_eq : Cardina
l.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `instIsLocalizedModuleQuotientSubmoduleLocalizedModuleLocalizationLocaliz
edToLocalizedQuotient`：∀ {R : Type u_5} {M : Type u_7} [inst : CommRing R] [inst
_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submonoid R) (M' : Subm
odu…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `IsLocalization.rank_eq`：IsLocalization.rank_eq : Module.rank S N = Modul
e.rank R N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `rank_quotient_add_rank_of_divisionRing`：rank_quotient_add_rank_of_divisi
onRing (p : Submodule K V) : Module.rank K (V ⧸ p) + Module.rank K p = Module.ra
nk K V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **rank-nullity theorem** for commutative domains. Also see `rank_quotient_ad
d_rank`.
-/
theorem rank_quotient_add_rank_of_isDomain [IsDomain R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' = Module.rank R M := by
  apply lift_injective.{max uR uM}
  simp_rw [lift_add, ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalized R⁰) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (LocalizedModule.mkLinearMap R⁰ M) le_rfl,
    ← IsLocalizedModule.lift_rank_eq R⁰ (M'.toLocalizedQuotient R⁰) le_rfl,
    ← IsLocalization.rank_eq (FractionRing R) R⁰ le_rfl,
    ← lift_add, rank_quotient_add_rank_of_divisionRing]

universe w in
/-
**IsDomain.hasRankNullity** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsDomain.hasRankNullity [IsDomain R] : HasRankNullity.{w} R where rank_quo
tient_add_rank
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_set_linearIndependent_of_isDomain`：exists_set_linearIndependent_o
f_isDomain [IsDomain R] : exists s : Set M, #s = Module.rank R M ∧ LinearIndepOn
 R id s
· 使用定理 `rank_quotient_add_rank_of_isDomain`：rank_quotient_add_rank_of_isDomain [
IsDomain R] (M' : Submodule R M) : Module.rank R (M ⧸ M') + Module.rank R M' = M
odule.rank R M
-/
instance IsDomain.hasRankNullity [IsDomain R] : HasRankNullity.{w} R where
  rank_quotient_add_rank := rank_quotient_add_rank_of_isDomain
  exists_set_linearIndependent M := exists_set_linearIndependent_of_isDomain R M

namespace IsBaseChange

open Cardinal TensorProduct

section

variable {p} [Free S N] [StrongRankCondition S] {T : Type uT} [CommRing T] [Algebra R T]
  (hpT : Algebra.algebraMapSubmonoid T p ≤ T⁰) [StrongRankCondition (S ⊗[R] T)]
  {P : Type uP} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  {g : M →ₗ[R] P} (bc : IsBaseChange T g)

include S hp hpT f bc

/-
**IsBaseChange.lift_rank_eq_of_le_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsB
aseChange`。
形式化陈述：lift_rank_eq_of_le_nonZeroDivisors : Cardinal.lift.{uM} (Module.rank T P) 
= Cardinal.lift.{uP} (Module.rank R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsLocalizedModule.lift_rank_eq`：IsLocalizedModule.lift_rank_eq : Cardina
l.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M)
· 使用引理 `IsLocalization.rank_eq`：IsLocalization.rank_eq : Module.rank S N = Modul
e.rank R N
· 使用定理 `Module.rank_baseChange`：Module.rank_baseChange : Module.rank R (R otimes
[S] M') = Cardinal.lift.{u} (Module.rank S M')
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
-/
theorem lift_rank_eq_of_le_nonZeroDivisors :
    Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.rank R M) := by
  rw [← lift_inj.{_, max uS uT uN}, lift_lift, lift_lift]
  let ST := S ⊗[R] T
  conv_rhs => rw [← lift_lift.{uN, max uS uT uP}, ← IsLocalizedModule.lift_rank_eq p f hp,
    ← IsLocalization.rank_eq S p hp, lift_lift, ← lift_lift.{max uS uT, max uM uP},
    ← rank_baseChange (R := ST), ← lift_id'.{max uS uT, max uS uT uN} (Module.rank ..),
    lift_lift, ← lift_lift.{max uS uT uP, uM}]
  let _ : Algebra T ST := Algebra.TensorProduct.rightAlgebra
  set pT := Algebra.algebraMapSubmonoid T p
  rw [← lift_lift.{max uS uT, max uM uN}, ← lift_umax.{uP},
    ← IsLocalizedModule.lift_rank_eq pT (mk T ST P 1) hpT,
    ← IsLocalization.rank_eq ST pT hpT, lift_id'.{uP, max uS uT},
    ← lift_id'.{max uS uT, max uS uT uP} (Module.rank ..), lift_lift,
    ← lift_lift.{max uS uT uN, uM}, lift_inj]
  exact LinearEquiv.lift_rank_eq <| AlgebraTensorModule.congr (.refl ST ST) bc.equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange .. ≪≫ₗ (AlgebraTensorModule.cancelBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl ..) ((isLocalizedModule_iff_isBaseChange p S f).mp ‹_›).equiv
/-
**IsBaseChange.finrank_eq_of_le_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsBas
eChange`。
形式化陈述：finrank_eq_of_le_nonZeroDivisors : finrank T P = finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsBaseChange.lift_rank_eq_of_le_nonZeroDivisors`：lift_rank_eq_of_le_nonZ
eroDivisors : Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.
rank R M)
-/
theorem finrank_eq_of_le_nonZeroDivisors : finrank T P = finrank R M := by
  simpa using! congr_arg toNat (lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc)

omit bc
/-
**IsBaseChange.rank_eq_of_le_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseCh
ange`。
形式化陈述：rank_eq_of_le_nonZeroDivisors {P : Type uM} [AddCommGroup P] [Module R P] 
[Module T P] [IsScalarTower R T P] {g : M ->ₗ[R] P} (bc : IsBaseChange T g) : Mo
dule.rank T P = Module.rank R M
参数：bc : IsBaseChange T g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsBaseChange.lift_rank_eq_of_le_nonZeroDivisors`：lift_rank_eq_of_le_nonZ
eroDivisors : Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.
rank R M)
-/
theorem rank_eq_of_le_nonZeroDivisors {P : Type uM} [AddCommGroup P] [Module R P] [Module T P]
    [IsScalarTower R T P] {g : M →ₗ[R] P} (bc : IsBaseChange T g) :
    Module.rank T P = Module.rank R M := by
  simpa using lift_rank_eq_of_le_nonZeroDivisors S f hp hpT bc

end

variable {p} {T : Type uT} [CommRing T] [NoZeroDivisors T] [Algebra R T] [FaithfulSMul R T]
  {P : Type uP} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
  {g : M →ₗ[R] P} (bc : IsBaseChange T g)

include bc

/-
**IsBaseChange.lift_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：lift_rank_eq : Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (
Module.rank R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `map_ne_zero_of_mem_nonZeroDivisors`：map_ne_zero_of_mem_nonZeroDivisors [
Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F) (hg : Injective (g : M₀ -> M₀')) 
{x : M₀} (h : x in M₀⁰) …
（共 53 条，此处仅展示前 30 条）
-/
theorem lift_rank_eq :
    Cardinal.lift.{uM} (Module.rank T P) = Cardinal.lift.{uP} (Module.rank R M) := by
  have inj := FaithfulSMul.algebraMap_injective R T
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R T).codomain_trivial; simp only [rank_subsingleton, lift_one]
  have := (isDomain_iff_noZeroDivisors_and_nontrivial T).mpr
    ⟨‹_›, (FaithfulSMul.algebraMap_injective R T).nontrivial⟩
  let FR := FractionRing R
  let FT := FractionRing T
  replace inj : Function.Injective (algebraMap R FT) := (IsFractionRing.injective T _).comp inj
  let g := TensorProduct.mk T FT P 1
  have : IsLocalizedModule R⁰ (TensorProduct.mk R FR FT 1) := inferInstance
  let _ : Algebra FT (FR ⊗[R] FT) := Algebra.TensorProduct.rightAlgebra
  let _ := isLocalizedModule_iff_isLocalization.mp this |>.atUnits _ _ ?_ |>.symm.isField
    (Field.toIsField FT) |>.toField
  on_goal 2 => rintro _ ⟨_, mem, rfl⟩; exact (map_ne_zero_of_mem_nonZeroDivisors _ inj mem).isUnit
  have := bc.comp_iff.2 ((isLocalizedModule_iff_isBaseChange T⁰ FT g).1 inferInstance)
  rw [← lift_inj.{_, max uT uP}, lift_lift, lift_lift, ← lift_lift.{max uT uP, uM},
    ← IsLocalizedModule.lift_rank_eq T⁰ g le_rfl, lift_lift, ← lift_lift.{uM},
    ← IsLocalization.rank_eq FT T⁰ le_rfl,
    lift_rank_eq_of_le_nonZeroDivisors FR (LocalizedModule.mkLinearMap R⁰ M) le_rfl
      (map_le_nonZeroDivisors_of_injective _ inj le_rfl) this, lift_lift]
/-
**IsBaseChange.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：finrank_eq : finrank T P = finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsBaseChange.lift_rank_eq`：lift_rank_eq : Cardinal.lift.{uM} (Module.ran
k T P) = Cardinal.lift.{uP} (Module.rank R M)
-/
theorem finrank_eq : finrank T P = finrank R M := by simpa using! congr_arg toNat bc.lift_rank_eq

omit bc
/-
**IsBaseChange.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：rank_eq {P : Type uM} [AddCommGroup P] [Module R P] [Module T P] [IsScalar
Tower R T P] {g : M ->ₗ[R] P} (bc : IsBaseChange T g) : Module.rank T P = Module
.rank R M
参数：bc : IsBaseChange T g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsBaseChange.lift_rank_eq`：lift_rank_eq : Cardinal.lift.{uM} (Module.ran
k T P) = Cardinal.lift.{uP} (Module.rank R M)
-/
theorem rank_eq {P : Type uM} [AddCommGroup P] [Module R P] [Module T P] [IsScalarTower R T P]
    {g : M →ₗ[R] P} (bc : IsBaseChange T g) : Module.rank T P = Module.rank R M := by
  simpa using bc.lift_rank_eq

end IsBaseChange

end CommRing

section Ring

variable {R} [Ring R] [IsDomain R]

/-- A domain that is not (left) Ore is of infinite rank.
See [cohn_1995] Proposition 1.3.6 -/
/-
**aleph0_le_rank_of_isEmpty_oreSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：aleph0_le_rank_of_isEmpty_oreSet (hS : IsEmpty (OreLocalization.OreSet R⁰)
) : ℵ₀ <= Module.rank R R
参数：hS : IsEmpty (OreLocalization.OreSet R⁰)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors`：nonempty_oreSet_i
ff_of_noZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submonoid R} :
 Nonempty (OreSet S) ↔ forall (r : R) (s : …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le`：aleph0_le {c : Cardinal} : ℵ₀ <= c ↔ forall n : Nat,
 ↑n <= c where mp h _
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
A domain that is not (left) Ore is of infinite rank.
See [cohn_1995] Proposition 1.3.6
-/
lemma aleph0_le_rank_of_isEmpty_oreSet (hS : IsEmpty (OreLocalization.OreSet R⁰)) :
    ℵ₀ ≤ Module.rank R R := by
  rw [← not_nonempty_iff, OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors] at hS
  push Not at hS
  obtain ⟨r, s, h⟩ := hS
  refine Cardinal.aleph0_le.mpr fun n ↦ ?_
  suffices LinearIndependent R (fun (i : Fin n) ↦ r * s ^ (i : ℕ)) by
    simpa using this.cardinal_lift_le_rank
  suffices ∀ (g : ℕ → R) (x), (∑ i ∈ Finset.range n, g i • (r * s ^ (i + x))) = 0 →
      ∀ i < n, g i = 0 by
    refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
    simpa only [dif_pos i.prop] using this (fun i ↦ if h : i < n then g ⟨i, h⟩ else 0) 0
      (by simp [← Fin.sum_univ_eq_sum_range, ← hg]) i i.prop
  intro g x hg i hin
  induction n generalizing g x i with
  | zero => contradiction
  | succ n IH =>
    rw [Finset.sum_range_succ'] at hg
    by_cases hg0 : g 0 = 0
    · simp only [hg0, zero_smul, add_zero, add_assoc] at hg
      cases i; exacts [hg0, IH _ _ hg _ (Nat.succ_lt_succ_iff.mp hin)]
    simp only [zero_add, pow_add _ _ x,
      ← mul_assoc, pow_succ, ← Finset.sum_mul, smul_eq_mul] at hg
    rw [← neg_eq_iff_add_eq_zero, ← neg_mul, ← neg_mul] at hg
    have := mul_right_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp (s ^ x).prop) hg
    exact (h _ ⟨(g 0), mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa)⟩ this.symm).elim

-- TODO: Upgrade this to an iff. See [lam_1999] Exercise 10.21
/-
**nonempty_oreSet_of_strongRankCondition** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonempty_oreSet_of_strongRankCondition [StrongRankCondition R] : Nonempty 
(OreLocalization.OreSet R⁰)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `aleph0_le_rank_of_isEmpty_oreSet`：aleph0_le_rank_of_isEmpty_oreSet (hS :
 IsEmpty (OreLocalization.OreSet R⁰)) : ℵ₀ <= Module.rank R R
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
lemma nonempty_oreSet_of_strongRankCondition [StrongRankCondition R] :
    Nonempty (OreLocalization.OreSet R⁰) := by
  by_contra! h
  have := aleph0_le_rank_of_isEmpty_oreSet h
  rw [rank_self] at this
  exact this.not_gt one_lt_aleph0

end Ring

