/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
## The Hopkins–Levitzki theorem

## Main results

* `IsSemiprimaryRing.isNoetherian_iff_isArtinian`: the Hopkins–Levitzki theorem, which states
  that for a module over a semiprimary ring (in particular, an Artinian ring),
  `IsNoetherian` is equivalent to `IsArtinian` (and therefore also to `IsFiniteLength`).

* In particular, for a module over an Artinian ring, `Module.Finite`, `IsNoetherian`, `IsArtinian`,
  and `IsFiniteLength` are all equivalent (`IsArtinianRing.tfae`),
  and a (left) Artinian ring is also (left) Noetherian.

* `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`: a commutative ring is Artinian iff
  it is Noetherian with Krull dimension at most 0.

## Reference

* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

public section

universe u

variable (R₀ R : Type*) (M : Type u) [Ring R₀] [Ring R] [Module R₀ R]
  [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]

namespace IsSemiprimaryRing

variable [IsSemiprimaryRing R]

/-
**IsSemiprimaryRing.induction** 是 Mathlib 中的一个定理，位于命名空间 `IsSemiprimaryRing`。
形式化陈述：∀ (R₀ : Type u_1) (R : Type u_2) (M : Type u) [inst : Ring R₀] [inst_1 : R
ing R] [inst_2 : _root_.Module R₀ R]   [inst_3 : AddCommGroup M] [inst_4 : _root
_.Module R₀ M] [inst_5 : _root_.Module R M] [IsScalarTower R₀ R M]   [IsSemiprim
aryRing R]   {P : (M : Type u) → [inst_8 : AddCommGroup M] → [_root_.Module R₀ M
] → [_root_.Module R M] → Prop},   (∀ (M : Type u) [inst_8 : AddCommGroup M] [in
st_9 : _root_.Module R₀ M] [inst_10 : _root_.Module R M]       [IsScalarTower R₀
 R M] [IsSemisimpleModule R M], Module.IsTorsionBySet R M ↑(Ring.jacobson R) → P
 M) →     (∀ (M : Type u) [inst_8 : AddCommGroup M] [inst_9 : _root_.Module R₀ M
] [inst_10 : _root_.Module R M]         [inst_11 : IsScalarTower R₀ R M],       
  have N := Ring.jacobson R • ⊤;         P ↥N → P (M ⧸ N) → P M) →       P M
参数：R₀ : Type u_1；R : Type u_2；M : Type u；M : Type u；∀ (M : Type u) [inst_8 : Add
CommGroup M] [inst_9 : _root_.Module R₀ M] [inst_10 : _root_.Module R M]       [
IsScalarTower R₀ R M] [IsSemisimpleModule R M], Module.IsTorsionBySet R M ↑(Ring
.jacobson R) → P M；∀ (M : Type u) [inst_8 : AddCommGroup M] [inst_9 : _root_.Mod
ule R₀ M] [inst_10 : _root_.Module R M]         [inst_11 : IsScalarTower R₀ R M]
,         have N := Ring.jacobson R • ⊤;         P ↥N → P (M ⧸ N) → P M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.instIsTwoSidedJacobson`：∀ (R : Type u_1) [inst : Ring R], (Ring.jac
obson R).IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSemiprimaryRing_iff`：∀ (R : Type u_1) [inst : Ring R],   IsSemiprimary
Ring R ↔ IsSemisimpleRing (R ⧸ Ring.jacobson R) ∧ IsNilpotent (Ring.jacobson R)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Module.isTorsionBySet_iff_subset_annihilator`：isTorsionBySet_iff_subset_
annihilator {s : Set R} : IsTorsionBySet R M s ↔ s subseteq annihilator R M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.isSemisimpleModule_iff_of_bijective`：∀ {R : Type u_2} {S : Typ
e u_3} [inst : Ring R] [inst_1 : Ring S] {M' : Type u_6} [inst_2 : AddCommGroup 
M']   [inst_3 : _root_.Module R M']…
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.pow_zero`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `Submodule.pow_one`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [inst
_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] (
M : Sub…
· 使用定理 `Submodule.le_annihilator_iff`：le_annihilator_iff {N : Submodule R M} {I 
: Ideal R} : I <= annihilator N ↔ I • N = ⊥
· 使用定理 `Submodule.mul_smul`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (I J : Ideal R)   (N : Submo
dule R M…
· 使用定理 `Submodule.pow_succ`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `Submodule.annihilator_top`：annihilator_top : (⊤ : Submodule R M).annihil
ator = Module.annihilator R M
· 使用定理 `Module.isTorsionBySet_quotient_iff`：isTorsionBySet_quotient_iff (N : Sub
module R M) (s : Set R) : IsTorsionBySet R (M ⧸ N) s ↔ forall x, forall r in s, 
r • x in N
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `trivial`：True
-/
@[elab_as_elim] protected theorem induction
    {P : ∀ (M : Type u) [AddCommGroup M] [Module R₀ M] [Module R M], Prop}
    (h0 : ∀ (M) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
      [IsSemisimpleModule R M], Module.IsTorsionBySet R M (Ring.jacobson R) → P M)
    (h1 : ∀ (M) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M],
      let N := Ring.jacobson R • (⊤ : Submodule R M); P N → P (M ⧸ N) → P M) :
    P M := by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n ≤ Module.annihilator R M := hn ▸ bot_le
  have {M} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M] :
      Jac ≤ Module.annihilator R M → P M := by
    rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator]
    intro h
    let _ := h.module
    have := (h.semilinearMap.isSemisimpleModule_iff_of_bijective Function.bijective_id).2
      inferInstance
    exact h0 _ h
  induction n generalizing M with
  | zero => rw [Jac.pow_zero, Ideal.one_eq_top] at hn; exact this (le_top.trans hn)
  | succ n ih => ?_
  obtain _ | n := n
  · rw [Jac.pow_one] at hn; exact this hn
  refine h1 _ (ih _ ?_) (ih _ ?_)
  · rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff, Jac.pow_succ,
      Submodule.mul_smul, ← Submodule.le_annihilator_iff] at hn
  · rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator,
      Module.isTorsionBySet_quotient_iff]
    exact fun m i hi ↦ Submodule.smul_mem_smul (Ideal.pow_le_self n.succ_ne_zero hi) trivial

section

variable [IsScalarTower R₀ R R] [Module.Finite R₀ (R ⧸ Ring.jacobson R)]

/-
**IsSemiprimaryRing.finite_of_isNoetherian_or_isArtinian** 是 Mathlib 中的一个定理，位于命名
空间 `IsSemiprimaryRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem finite_of_isNoetherian_or_isArtinian :
    IsNoetherian R M ∨ IsArtinian R M → Module.Finite R₀ M := by
  refine IsSemiprimaryRing.induction R₀ R M (P := fun M ↦ IsNoetherian R M ∨ IsArtinian R M →
    Module.Finite R₀ M) (fun M _ _ _ _ _ hJ h ↦ ?_) (fun M _ _ _ _ hs hq h ↦ ?_)
  · let _ := hJ.module
    have := IsSemisimpleModule.finite_tfae (R := R) (M := M)
    simp_rw [this.out 1 0, this.out 2 0, or_self,
      hJ.semilinearMap.finite_iff_of_bijective Function.bijective_id] at h
    exact .trans (R ⧸ Ring.jacobson R) M
  · let N := (Ring.jacobson R • ⊤ : Submodule R M).restrictScalars R₀
    have : Module.Finite R₀ N := by refine hs (h.imp ?_ ?_) <;> (intro; infer_instance)
    have : Module.Finite R₀ (M ⧸ N) := by refine hq (h.imp ?_ ?_) <;> (intro; infer_instance)
    exact .of_submodule_quotient N
/-
**IsSemiprimaryRing.finite_of_isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 `IsSemiprim
aryRing`。
形式化陈述：finite_of_isNoetherian [IsNoetherian R M] : Module.Finite R₀ M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.HopkinsLevitzki.0.IsSemiprimaryRing.finite_o
f_isNoetherian_or_isArtinian`：∀ (R₀ : Type u_1) (R : Type u_2) (M : Type u) [ins
t : Ring R₀] [inst_1 : Ring R] [inst_2 : _root_.Module R₀ R]   [inst_3 : AddComm
Group M] […
-/
theorem finite_of_isNoetherian [IsNoetherian R M] : Module.Finite R₀ M :=
  finite_of_isNoetherian_or_isArtinian R₀ R M (.inl ‹_›)
/-
**IsSemiprimaryRing.finite_of_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 `IsSemiprimar
yRing`。
形式化陈述：finite_of_isArtinian [IsArtinian R M] : Module.Finite R₀ M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.HopkinsLevitzki.0.IsSemiprimaryRing.finite_o
f_isNoetherian_or_isArtinian`：∀ (R₀ : Type u_1) (R : Type u_2) (M : Type u) [ins
t : Ring R₀] [inst_1 : Ring R] [inst_2 : _root_.Module R₀ R]   [inst_3 : AddComm
Group M] […
-/
theorem finite_of_isArtinian [IsArtinian R M] : Module.Finite R₀ M :=
  finite_of_isNoetherian_or_isArtinian R₀ R M (.inr ‹_›)

end

variable {R M}

/-
**IsSemiprimaryRing.isNoetherian_iff_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 `IsSem
iprimaryRing`。
形式化陈述：isNoetherian_iff_isArtinian : IsNoetherian R M ↔ IsArtinian R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemiprimaryRing.induction`：∀ (R₀ : Type u_1) (R : Type u_2) (M : Type 
u) [inst : Ring R₀] [inst_1 : Ring R] [inst_2 : _root_.Module R₀ R]   [inst_3 : 
AddCommGroup M] […
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsSemisimpleModule.finite_tfae`：IsSemisimpleModule.finite_tfae [IsSemisi
mpleModule R M] : List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M
, IsFiniteLength R M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherian_iff_submodule_quotient`：isNoetherian_iff_submodule_quotient
 (S : Submodule R N) : IsNoetherian R N ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸
 S)
· 使用定理 `isArtinian_iff_submodule_quotient`：isArtinian_iff_submodule_quotient (S 
: Submodule R P) : IsArtinian R P ↔ IsArtinian R S ∧ IsArtinian R (P ⧸ S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNoetherian_iff_isArtinian : IsNoetherian R M ↔ IsArtinian R M :=
  IsSemiprimaryRing.induction R R M (P := fun M ↦ IsNoetherian R M ↔ IsArtinian R M)
    (fun M _ _ _ _ _ _ ↦ IsSemisimpleModule.finite_tfae.out 1 2)
    fun M _ _ _ _ h h' ↦ let N : Submodule R M := Ring.jacobson R • ⊤; by
      simp_rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submodule_quotient N, N, h, h']
/-
**IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg** 是 Mathlib 中的一个定理，位于
命名空间 `IsSemiprimaryRing`。
形式化陈述：isNoetherian_iff_finite_of_jacobson_fg (fg : (Ring.jacobson R).FG) : IsNoe
therian R M ↔ Module.Finite R M
参数：fg : (Ring.jacobson R).FG。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSemiprimaryRing.induction`：∀ (R₀ : Type u_1) (R : Type u_2) (M : Type 
u) [inst : Ring R₀] [inst_1 : Ring R] [inst_2 : _root_.Module R₀ R]   [inst_3 : 
AddCommGroup M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsSemisimpleModule.finite_tfae`：IsSemisimpleModule.finite_tfae [IsSemisi
mpleModule R M] : List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M
, IsFiniteLength R M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherian_iff_submodule_quotient`：isNoetherian_iff_submodule_quotient
 (S : Submodule R N) : IsNoetherian R N ↔ IsNoetherian R S ∧ IsNoetherian R (N ⧸
 S)
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Submodule.FG.smul`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : Ideal R} [I.IsTwoS
ided] {…
· 使用定理 `Ring.instIsTwoSidedJacobson`：∀ (R : Type u_1) [inst : Ring R], (Ring.jac
obson R).IsTwoSided
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
theorem isNoetherian_iff_finite_of_jacobson_fg (fg : (Ring.jacobson R).FG) :
    IsNoetherian R M ↔ Module.Finite R M :=
  ⟨fun _ ↦ inferInstance, IsSemiprimaryRing.induction R R M
    (P := fun M ↦ Module.Finite R M → IsNoetherian R M)
    (fun M _ _ _ _ _ _ ↦ (IsSemisimpleModule.finite_tfae.out 0 1).mp)
    fun M _ _ _ _ hs hq fin ↦ (isNoetherian_iff_submodule_quotient (Ring.jacobson R • ⊤)).mpr
      ⟨hs (.of_fg (.smul fg fin.1)), hq inferInstance⟩⟩
/-
**IsSemiprimaryRing.isNoetherianRing_iff_jacobson_fg** 是 Mathlib 中的一个定理，位于命名空间 `
IsSemiprimaryRing`。
形式化陈述：isNoetherianRing_iff_jacobson_fg : IsNoetherianRing R ↔ (Ring.jacobson R).
FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg`：isNoetherian_i
ff_finite_of_jacobson_fg (fg : (Ring.jacobson R).FG) : IsNoetherian R M ↔ Module
.Finite R M
-/
theorem isNoetherianRing_iff_jacobson_fg : IsNoetherianRing R ↔ (Ring.jacobson R).FG :=
  ⟨fun _ ↦ IsNoetherian.noetherian .., fun fg ↦
    (IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg fg).mpr inferInstance⟩

end IsSemiprimaryRing

/-
**IsArtinianRing.tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsArtinianRing.tfae [IsArtinianRing R] : List.TFAE [Module.Finite R M, IsN
oetherian R M, IsArtinian R M, IsFiniteLength R M]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemiprimaryRing.isNoetherian_iff_isArtinian`：isNoetherian_iff_isArtini
an : IsNoetherian R M ↔ IsArtinian R M
· 使用定理 `IsArtinianRing.instIsSemiprimaryRing`：∀ {R : Type u_1} [inst : Ring R] [
IsArtinianRing R], IsSemiprimaryRing R
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsArtinianRing.tfae [IsArtinianRing R] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M] := by
  tfae_have 2 ↔ 3 := IsSemiprimaryRing.isNoetherian_iff_isArtinian
  tfae_have 2 → 1 := fun _ ↦ inferInstance
  tfae_have 1 → 3 := fun _ ↦ inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tfae_have 4 → 2 := And.left
  tfae_have 2 → 4 := fun h ↦ ⟨h, tfae_2_iff_3.mp h⟩
  tfae_finish

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself."]
/-
**isArtinianRing_iff_isFiniteLength** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinianRing_iff_isFiniteLength : IsArtinianRing R ↔ IsFiniteLength R R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsArtinianRing.tfae`：IsArtinianRing.tfae [IsArtinianRing R] : List.TFAE 
[Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
-/
theorem isArtinianRing_iff_isFiniteLength : IsArtinianRing R ↔ IsFiniteLength R R :=
  ⟨fun h ↦ ((IsArtinianRing.tfae R R).out 2 3).mp h,
    fun h ↦ (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2⟩

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself.
**Any such ring is both Artinian and Noetherian.**"]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsArtinianRing R] : IsNoetherianRing R := ((IsArtinianRing.tfae R R).out 2 1).mp ‹_›

/-- A finitely generated Artinian module over a commutative ring is Noetherian. This is not
necessarily the case over a noncommutative ring, see https://mathoverflow.net/a/61700. -/
/-
**isNoetherian_of_finite_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_finite_isArtinian {R} [CommRing R] [Module R M] [Module.Fi
nite R M] [IsArtinian R M] : IsNoetherian R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isNoetherian_top_iff`：isNoetherian_top_iff : IsNoetherian R (⊤ : Submodu
le R M) ↔ IsNoetherian R M
· 使用定理 `Submodule.span_iUnion`：span_iUnion {ι} (s : ι -> Set M) : span R (⋃ i, s
 i) = ⨆ i, span R (s i)
· 使用定理 `Set.iUnion_of_singleton_coe`：iUnion_of_singleton_coe (s : Set α) : ⋃ i :
 s, ({(i : α)} : Set α) = s
· 使用定理 `LinearMap.span_singleton_eq_range`：span_singleton_eq_range (x : M) : R ∙
 x = range (toSpanSingleton R M x)
· 使用定理 `LinearEquiv.isNoetherian_iff`：LinearEquiv.isNoetherian_iff {σ : R ->+* S
} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) :
 IsNoetherian R M …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `LinearMap.isNoetherian_iff_of_bijective`：LinearMap.isNoetherian_iff_of_b
ijective {S P} [Semiring S] [AddCommMonoid P] [Module S P] {σ : R ->+* S} [RingH
omSurjective σ] (l : M ->ₛₗ[σ…
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `IsArtinianRing.eq_1`：∀ (R : Type u_1) [inst : Semiring R], IsArtinianRin
g R = IsArtinian R R
· 使用定理 `LinearMap.isArtinian_iff_of_bijective`：LinearMap.isArtinian_iff_of_bijec
tive {S P} [Semiring S] [AddCommMonoid P] [Module S P] {σ : R ->+* S} [RingHomSu
rjective σ] (l : M ->ₛₗ[σ] …
· 使用定理 `LinearEquiv.isArtinian_iff`：LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) :
 IsArtinian R M ↔ IsArtinian R P
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite

--- 原说明 ---
A finitely generated Artinian module over a commutative ring is Noetherian. This
 is not
necessarily the case over a noncommutative ring, see https://mathoverflow.net/a/
61700.
-/
theorem isNoetherian_of_finite_isArtinian {R} [CommRing R] [Module R M]
    [Module.Finite R M] [IsArtinian R M] : IsNoetherian R M := by
  obtain ⟨s, fin, span⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  rw [← s.iUnion_of_singleton_coe, Submodule.span_iUnion] at span
  rw [← Set.finite_coe_iff] at fin
  rw [← isNoetherian_top_iff, ← span]
  have _ (i : M) : IsNoetherian R (Submodule.span R {i}) := by
    rw [LinearMap.span_singleton_eq_range, ← (LinearMap.quotKerEquivRange _).isNoetherian_iff]
    let e (I : Ideal R) : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨.id _, fun _ _ ↦ rfl⟩
    rw [(e _).isNoetherian_iff_of_bijective Function.bijective_id]
    refine @instIsNoetherianRingOfIsArtinianRing _ _ ?_
    rw [IsArtinianRing, ← (e _).isArtinian_iff_of_bijective Function.bijective_id,
      (LinearMap.quotKerEquivRange _).isArtinian_iff]
    infer_instance
  infer_instance
/-
**IsNoetherianRing.isArtinianRing_of_krullDimLE_zero** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsNoetherianRing.isArtinianRing_of_krullDimLE_zero {R} [CommRing R] [IsNoe
therianRing R] [Ring.KrullDimLE 0 R] : IsArtinianRing R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.jacobson_eq_nilradical_of_krullDimLE_zero`：Ring.jacobson_eq_nilradi
cal_of_krullDimLE_zero (R) [CommRing R] [KrullDimLE 0 R] : jacobson R = nilradic
al R
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `minimalPrimes.finite_of_isNoetherianRing`：minimalPrimes.finite_of_isNoet
herianRing : (minimalPrimes R).Finite
· 使用引理 `Ideal.mem_minimalPrimes_of_krullDimLE_zero`：Ideal.mem_minimalPrimes_of_k
rullDimLE_zero [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime] : I in minimalPri
mes R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `instIsMaximalOfIsPrimeOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : Com
mSemiring R] (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R], I.IsMaximal
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `RingEquiv.isSemisimpleRing`：RingEquiv.isSemisimpleRing (e : R ≃+* S) [Is
SemisimpleRing R] : IsSemisimpleRing S where __
· 使用定理 `Ideal.isCoprime_of_isMaximal`：isCoprime_of_isMaximal [I.IsMaximal] [J.Is
Maximal] (ne : I != J) : IsCoprime I J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `instIsSemisimpleRingForallOfFinite`：∀ {ι : Type u_7} [Finite ι] (R : ι →
 Type u_6) [inst : (i : ι) → Ring (R i)] [∀ (i : ι), IsSemisimpleRing (R i)],   
IsSemisimpleRing ((i : ι…
· 使用定理 `IsNoetherianRing.isNilpotent_nilradical`：IsNoetherianRing.isNilpotent_ni
lradical (R : Type*) [CommSemiring R] [IsNoetherianRing R] : IsNilpotent (nilrad
ical R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsSemiprimaryRing.isNoetherian_iff_isArtinian`：isNoetherian_iff_isArtini
an : IsNoetherian R M ↔ IsArtinian R M
-/
theorem IsNoetherianRing.isArtinianRing_of_krullDimLE_zero {R} [CommRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 0 R] : IsArtinianRing R :=
  have eq := Ring.jacobson_eq_nilradical_of_krullDimLE_zero R
  let Spec := {I : Ideal R | I.IsPrime}
  have : Finite Spec :=
    (minimalPrimes.finite_of_isNoetherianRing R).subset Ideal.mem_minimalPrimes_of_krullDimLE_zero
  have (I : Spec) : I.1.IsPrime := I.2
  have (I : Spec) : IsSemisimpleRing (R ⧸ I.1) := let _ := Ideal.Quotient.field I.1; inferInstance
  have : IsSemisimpleRing (R ⧸ Ring.jacobson R) := by
    rw [eq, nilradical_eq_sInf, sInf_eq_iInf']
    exact (Ideal.quotientInfRingEquivPiQuotient _ fun I J ne ↦
      Ideal.isCoprime_of_isMaximal <| Subtype.coe_ne_coe.mpr ne).symm.isSemisimpleRing
  have : IsSemiprimaryRing R := ⟨this, eq ▸ IsNoetherianRing.isNilpotent_nilradical R⟩
  IsSemiprimaryRing.isNoetherian_iff_isArtinian.mp ‹_›
/-
**isArtinianRing_iff_isNoetherianRing_krullDimLE_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：∀ {R : Type u_3} [inst : CommRing R], IsArtinianRing R ↔ IsNoetherianRing 
R ∧ Ring.KrullDimLE 0 R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`：IsNoetherianRing.isA
rtinianRing_of_krullDimLE_zero {R} [CommRing R] [IsNoetherianRing R] [Ring.Krull
DimLE 0 R] : IsArtinianRing R
-/
@[stacks 00KH] theorem isArtinianRing_iff_isNoetherianRing_krullDimLE_zero {R} [CommRing R] :
    IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨h, _⟩ ↦ h.isArtinianRing_of_krullDimLE_zero⟩
/-
**isArtinianRing_iff_krullDimLE_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isArtinianRing_iff_krullDimLE_zero {R : Type*} [CommRing R] [IsNoetherianR
ing R] : IsArtinianRing R ↔ Ring.KrullDimLE 0 R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`：∀ {R : Type u_3} [i
nst : CommRing R], IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isArtinianRing_iff_krullDimLE_zero {R : Type*} [CommRing R] [IsNoetherianRing R] :
    IsArtinianRing R ↔ Ring.KrullDimLE 0 R := by
  rwa [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, and_iff_right]
/-
**isArtinianRing_iff_isNilpotent_maximalIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isArtinianRing_iff_isNilpotent_maximalIdeal (R : Type*) [CommRing R] [IsNo
etherianRing R] [IsLocalRing R] : IsArtinianRing R ↔ IsNilpotent (IsLocalRing.ma
ximalIdeal R)
参数：R : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isArtinianRing_iff_krullDimLE_zero`：isArtinianRing_iff_krullDimLE_zero {
R : Type*} [CommRing R] [IsNoetherianRing R] : IsArtinianRing R ↔ Ring.KrullDimL
E 0 R
· 使用引理 `Ideal.FG.isNilpotent_iff_le_nilradical`：Ideal.FG.isNilpotent_iff_le_nilr
adical {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I.FG) : IsNilpotent I ↔ 
I <= nilradical R
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `Ring.krullDimLE_zero_and_isLocalRing_tfae`：Ring.krullDimLE_zero_and_isLo
calRing_tfae : List.TFAE [ Ring.KrullDimLE 0 R ∧ IsLocalRing R, exists! I : Idea
l R, I.IsPrime, forall x : R, I…
· 使用定理 `IsLocalRing.isMaximal_iff`：isMaximal_iff {I : Ideal R} : I.IsMaximal ↔ I
 = maximalIdeal R where mp hI
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isArtinianRing_iff_isNilpotent_maximalIdeal (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : IsArtinianRing R ↔ IsNilpotent (IsLocalRing.maximalIdeal R) := by
  rw [isArtinianRing_iff_krullDimLE_zero,
    Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _),
    ← and_iff_left (a := Ring.KrullDimLE 0 R) ‹IsLocalRing R›,
    (Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 3 rfl rfl,
    IsLocalRing.isMaximal_iff, le_antisymm_iff, and_iff_right]
  exact IsLocalRing.le_maximalIdeal (by simp [nilradical, Ideal.radical_eq_top])
