/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Data.Fintype.Quotient

/-!
# `DFinsupp` on `Sigma` types

## Main definitions

* `DFinsupp.sigmaCurry`: turn a `DFinsupp` indexed by a `Sigma` type into a `DFinsupp` with two
  parameters.
* `DFinsupp.sigmaUncurry`: turn a `DFinsupp` with two parameters into a `DFinsupp` indexed by a
  `Sigma` type. Inverse of `DFinsupp.sigmaCurry`.
* `DFinsupp.sigmaCurryEquiv`: `DFinsupp.sigmaCurry` and `DFinsupp.sigmaUncurry` bundled into a
  bijection.

-/

@[expose] public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Equiv

open Finset

variable {κ : Type*}

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

variable [DecidableEq ι]

/-- The natural map between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`. -/
/-
**DFinsupp.sigmaCurry** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurry [forall i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) : Π
₀ (i) (j), δ i j where toFun
参数：δ i j；f : Π₀ (i : Σ _, _), δ i.1 i.2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i 
j`.
-/
def sigmaCurry [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    Π₀ (i) (j), δ i j where
  toFun := fun i ↦
  { toFun := fun j ↦ f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ ↦
      ⟨m.filterMap (fun ⟨i', j'⟩ ↦ if h : i' = i then some <| h.rec j' else none),
        fun j ↦ (hm ⟨i, j⟩).imp_left (fun h ↦ (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.map (fun ⟨m, hm⟩ ↦
    ⟨m.map Sigma.fst, fun i ↦ Decidable.or_iff_not_imp_left.mpr (fun h ↦ DFinsupp.ext
      (fun j ↦ (hm ⟨i, j⟩).resolve_left (fun H ↦ (Multiset.mem_map.not.mp h) ⟨⟨i, j⟩, H, rfl⟩)))⟩)

@[simp]
/-
**DFinsupp.sigmaCurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurry_apply [forall i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.
2) (i : ι) (j : α i) : sigmaCurry f i j = f ⟨i, j⟩
参数：δ i j；f : Π₀ (i : Σ _, _), δ i.1 i.2；i : ι；j : α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaCurry_apply [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  rfl

@[simp]
/-
**DFinsupp.sigmaCurry_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurry_zero [forall i j, Zero (δ i j)] : sigmaCurry (0 : Π₀ (i : Σ _, 
_), δ i.1 i.2) = 0
参数：δ i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaCurry_zero [∀ i j, Zero (δ i j)] :
    sigmaCurry (0 : Π₀ (i : Σ _, _), δ i.1 i.2) = 0 :=
  rfl

@[simp]
/-
**DFinsupp.sigmaCurry_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurry_add [forall i j, AddZeroClass (δ i j)] (f g : Π₀ (i : Σ _, _), 
δ i.1 i.2) : sigmaCurry (f + g) = (sigmaCurry f + sigmaCurry g : Π₀ (i) (j), δ i
 j)
参数：δ i j；f g : Π₀ (i : Σ _, _), δ i.1 i.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem sigmaCurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (f + g) = (sigmaCurry f + sigmaCurry g : Π₀ (i) (j), δ i j) := by
  ext (i j)
  rfl

@[simp]
/-
**DFinsupp.sigmaCurry_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurry_smul [Monoid γ] [forall i j, AddMonoid (δ i j)] [forall i j, Di
stribMulAction γ (δ i j)] (r : γ) (f : Π₀ (i : Σ _, _), δ i.1 i.2) : sigmaCurry 
(r • f) = (r • sigmaCurry f : Π₀ (i) (j), δ i j)
参数：δ i j；δ i j；r : γ；f : Π₀ (i : Σ _, _), δ i.1 i.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem sigmaCurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)] [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (r • f) = (r • sigmaCurry f : Π₀ (i) (j), δ i j) := by
  ext (i j)
  rfl

@[simp]
/-
**DFinsupp.sigmaCurry_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurry_single [forall i, DecidableEq (α i)] [forall i j, Zero (δ i j)]
 (ij : Σ i, α i) (x : δ ij.1 ij.2) : sigmaCurry (single ij x) = single ij.1 (sin
gle ij.2 x : Π₀ j, δ ij.1 j)
参数：α i；δ i j；ij : Σ i, α i；x : δ ij.1 ij.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sigmaCurry_apply`：sigmaCurry_apply [forall i j, Zero (δ i j)] (
f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i) : sigmaCurry f i j = f ⟨i, j⟩
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem sigmaCurry_single [∀ i, DecidableEq (α i)] [∀ i j, Zero (δ i j)]
    (ij : Σ i, α i) (x : δ ij.1 ij.2) :
    sigmaCurry (single ij x) = single ij.1 (single ij.2 x : Π₀ j, δ ij.1 j) := by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp only
  rw [sigmaCurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · simp [hi]

/-- The natural map between `Π₀ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`. -/
/-
**DFinsupp.sigmaUncurry** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sigmaUncurry [forall i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) : Π₀ i : Σ
 _, _, δ i.1 i.2 where toFun i
参数：δ i j；f : Π₀ (i) (j), δ i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between `Π₀ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.
2`, inverse of
`curry`.
-/
def sigmaUncurry [∀ i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) : Π₀ i : Σ _, _, δ i.1 i.2 where
  toFun i := f i.1 i.2
  support' :=
    f.support'.bind fun s =>
      (Trunc.finChoice (fun i : ↥s.val.toFinset => (f i).support')).map fun fs =>
        ⟨s.val.toFinset.attach.val.bind fun i => (fs i).val.map (Sigma.mk i.val), by
          rintro ⟨i, a⟩
          cases s.prop i with
          | inl hi =>
            cases (fs ⟨i, Multiset.mem_toFinset.mpr hi⟩).prop a with
            | inl ha =>
              left; rw [Multiset.mem_bind]
              use ⟨i, Multiset.mem_toFinset.mpr hi⟩
              constructor
              case right => simp [ha]
              case left => apply Multiset.mem_attach
            | inr ha => right; simp [toFun_eq_coe (f i) ▸ ha]
          | inr hi => right; simp [toFun_eq_coe f ▸ hi]⟩

@[simp]
/-
**DFinsupp.sigmaUncurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaUncurry_apply [forall i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) (i :
 ι) (j : α i) : sigmaUncurry f ⟨i, j⟩ = f i j
参数：δ i j；f : Π₀ (i) (j), δ i j；i : ι；j : α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaUncurry_apply [∀ i j, Zero (δ i j)]
    (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  rfl

@[simp]
/-
**DFinsupp.sigmaUncurry_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaUncurry_zero [forall i j, Zero (δ i j)] : sigmaUncurry (0 : Π₀ (i) (j
), δ i j) = 0
参数：δ i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaUncurry_zero [∀ i j, Zero (δ i j)] :
    sigmaUncurry (0 : Π₀ (i) (j), δ i j) = 0 :=
  rfl

@[simp]
/-
**DFinsupp.sigmaUncurry_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaUncurry_add [forall i j, AddZeroClass (δ i j)] (f g : Π₀ (i) (j), δ i
 j) : sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g
参数：δ i j；f g : Π₀ (i) (j), δ i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem sigmaUncurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ (i) (j), δ i j) :
    sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g :=
  DFunLike.coe_injective rfl

@[simp]
/-
**DFinsupp.sigmaUncurry_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaUncurry_smul [Monoid γ] [forall i j, AddMonoid (δ i j)] [forall i j, 
DistribMulAction γ (δ i j)] (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • 
f) = r • sigmaUncurry f
参数：δ i j；δ i j；r : γ；f : Π₀ (i) (j), δ i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem sigmaUncurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f :=
  DFunLike.coe_injective rfl

@[simp]
/-
**DFinsupp.sigmaUncurry_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sigmaUncurry_single [forall i j, Zero (δ i j)] [forall i, DecidableEq (α i
)] (i) (j : α i) (x : δ i j) : sigmaUncurry (single i (single j x : Π₀ j : α i, 
δ i j)) = single ⟨i, j⟩ (by exact x)
参数：δ i j；α i；i；j : α i；x : δ i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sigmaUncurry_apply`：sigmaUncurry_apply [forall i j, Zero (δ i j
)] (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) : sigmaUncurry f ⟨i, j⟩ = f i j
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem sigmaUncurry_single [∀ i j, Zero (δ i j)] [∀ i, DecidableEq (α i)]
    (i) (j : α i) (x : δ i j) :
    sigmaUncurry (single i (single j x : Π₀ j : α i, δ i j)) = single ⟨i, j⟩ (by exact x) := by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigmaUncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j' j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · simp [hi]

/-- The natural bijection between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.

This is the dfinsupp version of `Equiv.piCurry`. -/
/-
**DFinsupp.sigmaCurryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurryEquiv [forall i j, Zero (δ i j)] : (Π₀ i : Σ _, _, δ i.1 i.2) ≃ 
Π₀ (i) (j), δ i j where toFun
参数：δ i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural bijection between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i)
, δ i j`.

This is the dfinsupp version of `Equiv.piCurry`.
-/
def sigmaCurryEquiv [∀ i j, Zero (δ i j)] : (Π₀ i : Σ _, _, δ i.1 i.2) ≃ Π₀ (i) (j), δ i j where
  toFun := sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigmaUncurry_apply, sigmaCurry_apply]
  right_inv f := by
    ext i j
    rw [sigmaCurry_apply, sigmaUncurry_apply]

end SigmaCurry

end Equiv

end DFinsupp

