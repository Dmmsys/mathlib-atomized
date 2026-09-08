/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Module.Basic

/-!
# Archimedean classes for ordered module

## Main definitions
* `ArchimedeanClass.ball` are `ArchimedeanClass.ballAddSubgroup` as a submodules.
* `ArchimedeanClass.closedBall` are `ArchimedeanClass.closedBallAddSubgroup` as a submodules.
-/

@[expose] public section

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

namespace ArchimedeanClass

@[simp]
/-
**ArchimedeanClass.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_smul (a : M) {k : K} (h : k != 0) : mk (k • a) = mk a
参数：a : M；h : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_smul`：abs_smul (a : R) (b : M) : |a • b| = |a| • |b|
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `le_smul_of_one_le_left`：le_smul_of_one_le_left [SMulPosMono α β] (hb : 0
 <= b) (h : 1 <= a) : b <= a • b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
-/
theorem mk_smul (a : M) {k : K} (h : k ≠ 0) : mk (k • a) = mk a := by
  have : Nontrivial K := nontrivial_iff.mpr ⟨k, 0, h⟩
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (show 0 < |k| by simpa using h)
  obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
  simp_rw [mk_eq_mk, abs_smul]
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← smul_assoc]
    exact le_smul_of_one_le_left (by simp) hm
  · have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this]
    exact smul_le_smul_of_nonneg_right hn (by simp)
/-
**ArchimedeanClass.mk_le_mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_le_mk_smul (a : M) (k : K) : mk a <= mk (k • a)
参数：a : M；k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_smul`：mk_smul (a : M) {k : K} (h : k != 0) : mk (k •
 a) = mk a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mk_le_mk_smul (a : M) (k : K) : mk a ≤ mk (k • a) := by
  obtain rfl | h := eq_or_ne k 0 <;> simp [*]

end ArchimedeanClass

namespace FiniteArchimedeanClass

variable (K)

/-- Given an upper set `s` of finite archimedean classes in a linearly ordered module `M` with
Archimedean scalars, all elements belonging to these classes together with 0 form a submodule.

This has the same carrier as `FiniteArchimedeanClass.addSubgroup`. -/
noncomputable
/-
**FiniteArchimedeanClass.submodule** 是 Mathlib 中的一个定义，位于命名空间 `FiniteArchimedeanC
lass`。
形式化陈述：submodule (s : UpperSet (FiniteArchimedeanClass M)) : Submodule K M where 
__
参数：s : UpperSet (FiniteArchimedeanClass M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def submodule (s : UpperSet (FiniteArchimedeanClass M)) : Submodule K M where
  __ := addSubgroup s
  smul_mem' k {a} ha ne := s.upper (ArchimedeanClass.mk_le_mk_smul ..) <|
    ha fun eq ↦ ne <| by simp [ArchimedeanClass.mk_eq_top_iff.mp eq]
/-
**FiniteArchimedeanClass.submodule_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `FiniteA
rchimedeanClass`。
形式化陈述：submodule_strictAnti : StrictAnti (submodule K (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteArchimedeanClass.addSubgroup_strictAnti`：∀ {M : Type u_1} [inst : 
AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M],   Stri
ctAnti FiniteArchimedeanClass.addSu…
-/
theorem submodule_strictAnti : StrictAnti (submodule K (M := M)) := addSubgroup_strictAnti

/-- An open ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.ballAddSubgroup`'s. -/
noncomputable
/-
**FiniteArchimedeanClass.ball** 是 Mathlib 中的一个缩写定义，位于命名空间 `FiniteArchimedeanClas
s`。
形式化陈述：ball (c : FiniteArchimedeanClass M)
参数：c : FiniteArchimedeanClass M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ball (c : FiniteArchimedeanClass M) := submodule K (UpperSet.Ioi c)

/-- A closed ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ici c`.

This has the same carrier as `ArchimedeanClass.closedBallAddSubgroup`'s. -/
noncomputable
/-
**FiniteArchimedeanClass.closedBall** 是 Mathlib 中的一个缩写定义，位于命名空间 `FiniteArchimede
anClass`。
形式化陈述：closedBall (c : FiniteArchimedeanClass M)
参数：c : FiniteArchimedeanClass M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev closedBall (c : FiniteArchimedeanClass M) := submodule K (UpperSet.Ici c)

@[simp]
/-
**FiniteArchimedeanClass.toAddSubgroup_ball** 是 Mathlib 中的一个定理，位于命名空间 `FiniteArc
himedeanClass`。
形式化陈述：toAddSubgroup_ball (c : FiniteArchimedeanClass M) : (ball K c).toAddSubgro
up = ballAddSubgroup c
参数：c : FiniteArchimedeanClass M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_ball (c : FiniteArchimedeanClass M) :
    (ball K c).toAddSubgroup = ballAddSubgroup c := rfl

@[simp]
/-
**FiniteArchimedeanClass.toAddSubgroup_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Fin
iteArchimedeanClass`。
形式化陈述：toAddSubgroup_closedBall (c : FiniteArchimedeanClass M) : (closedBall K c)
.toAddSubgroup = closedBallAddSubgroup c
参数：c : FiniteArchimedeanClass M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_closedBall (c : FiniteArchimedeanClass M) :
    (closedBall K c).toAddSubgroup = closedBallAddSubgroup c := rfl

@[simp]
/-
**FiniteArchimedeanClass.mem_ball_iff** 是 Mathlib 中的一个定理，位于命名空间 `FiniteArchimede
anClass`。
形式化陈述：mem_ball_iff {a : M} {c : FiniteArchimedeanClass M} : a in ball K c ↔ fora
ll h : a != 0, c < mk a h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteArchimedeanClass.mem_ballAddSubgroup_iff`：∀ {M : Type u_1} [inst :
 AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a : M
}   {c : FiniteArchimedeanClass M}, …
-/
theorem mem_ball_iff {a : M} {c : FiniteArchimedeanClass M} :
    a ∈ ball K c ↔ ∀ h : a ≠ 0, c < mk a h :=
  mem_ballAddSubgroup_iff

@[simp]
/-
**FiniteArchimedeanClass.mem_closedBall_iff** 是 Mathlib 中的一个定理，位于命名空间 `FiniteArc
himedeanClass`。
形式化陈述：mem_closedBall_iff {a : M} {c : FiniteArchimedeanClass M} : a in closedBal
l K c ↔ forall h : a != 0, c <= mk a h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff`：∀ {M : Type u_1} [
inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] 
{a : M}   {c : FiniteArchimedeanClass M}, …
-/
theorem mem_closedBall_iff {a : M} {c : FiniteArchimedeanClass M} :
    a ∈ closedBall K c ↔ ∀ h : a ≠ 0, c ≤ mk a h :=
  mem_closedBallAddSubgroup_iff
/-
**FiniteArchimedeanClass.ball_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `FiniteArchim
edeanClass`。
形式化陈述：ball_strictAnti : StrictAnti (ball (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteArchimedeanClass.ballAddSubgroup_strictAnti`：∀ {M : Type u_1} [ins
t : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M],   
StrictAnti FiniteArchimedeanClass.ballA…
-/
theorem ball_strictAnti : StrictAnti (ball (M := M) K) := ballAddSubgroup_strictAnti
/-
**FiniteArchimedeanClass.ball_lt_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `FiniteArc
himedeanClass`。
形式化陈述：ball_lt_closedBall {c : FiniteArchimedeanClass M} : ball K c < closedBall 
K c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteArchimedeanClass.submodule_strictAnti`：submodule_strictAnti : Stri
ctAnti (submodule K (M
· 使用定理 `Set.Ioi_ssubset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, 
Set.Ioi a ⊂ Set.Ici a
-/
theorem ball_lt_closedBall {c : FiniteArchimedeanClass M} : ball K c < closedBall K c :=
  submodule_strictAnti _ Set.Ioi_ssubset_Ici_self

end FiniteArchimedeanClass

