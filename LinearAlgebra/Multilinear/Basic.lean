/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.FunLike.Group
public import Mathlib.Data.FunLike.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset


/-!
# Multilinear maps

We define multilinear maps as maps from `∀ (i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`MultilinearMap R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `MultilinearMap R M₁ M₂` is the space of multilinear maps from `∀ (i : ι), M₁ i` to `M₂`.
* `f.map_update_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_update_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing

  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

See `Mathlib/LinearAlgebra/Multilinear/Curry.lean` for the currying of multilinear maps.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:

* fixing a vector `m : ∀ (j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : ∀ j, M₁ j`, and then modifying its `i`-th coordinate

The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`Function.update` that allows to change the value of `m` at `i`.

Note that the use of `Function.update` requires a `DecidableEq ι` term to appear somewhere in the
statement of `MultilinearMap.map_update_add'` and `MultilinearMap.map_update_smul'`.
Three possible choices are:

1. Requiring `DecidableEq ι` as an argument to `MultilinearMap` (as we did originally).
2. Using `Classical.decEq ι` in the statement of `map_add'` and `map_smul'`.
3. Quantifying over all possible `DecidableEq ι` instances in the statement of `map_add'` and
   `map_smul'`.

Option 1 works fine, but puts unnecessary constraints on the user
(the zero map certainly does not need decidability).
Option 2 looks great at first, but in the common case when `ι = Fin n`
it introduces non-defeq decidability instance diamonds
within the context of proving `map_update_add'` and `map_update_smul'`,
of the form `Fin.decidableEq n = Classical.decEq (Fin n)`.
Option 3 of course does something similar, but of the form `Fin.decidableEq n = _inst`,
which is much easier to clean up since `_inst` is a free variable
and so the equality can just be substituted.
-/

@[expose] public section

open Fin Function Finset Set

universe uR uS uι v v' v₁ v₁' v₁'' v₂ v₃ v₄

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}
variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

-- Don't generate injectivity lemmas, which the `simpNF` linter will time out on.
set_option genInjectivity false in
/-- Multilinear maps over the ring `R`, from `∀ i, M₁ i` to `M₂` where `M₁ i` and `M₂` are modules
over `R`. -/
/-
**MultilinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type uR) →   {ι : Type uι} →     (M₁ : ι → Type v₁) →       (M₂ : Typ
e v₂) →         [inst : Semiring R] →           [inst_1 : (i : ι) → AddCommMonoi
d (M₁ i)] →             [inst_2 : AddCommMonoid M₂] →               [(i : ι) → _
root_.Module R (M₁ i)] → [_root_.Module R M₂] → Type (max (max uι v₁) v₂)
参数：max uι v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multilinear maps over the ring `R`, from `∀ i, M₁ i` to `M₂` where `M₁ i` and `M
₂` are modules
over `R`.
-/
structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [Semiring R]
  [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : (∀ i, M₁ i) → M₂
  /-- A multilinear map is additive in every argument. -/
  map_update_add' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A multilinear map is compatible with scalar multiplication in every argument. -/
  map_update_smul' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      toFun (update m i (c • x)) = c • toFun (update m i x)

namespace MultilinearMap

section Semiring

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

initialize_simps_projections MultilinearMap (toFun → apply)

/-- Constructor for `MultilinearMap R M₁ M₂` when the
index type `ι` is already endowed with a `DecidableEq` instance. -/
@[simps]
/-
**MultilinearMap.mk'** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：mk' [DecidableEq ι] (f : (forall i, M₁ i) -> M₂) (h₁ : forall (m : forall 
i, M₁ i) (i : ι) (x y : M₁ i), f (update m i (x + y)) = f (update m i x) + f (up
date m i y)
参数：f : (forall i, M₁ i) -> M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `MultilinearMap R M₁ M₂` when the
index type `ι` is already endowed with a `DecidableEq` instance.
-/
def mk' [DecidableEq ι] (f : (∀ i, M₁ i) → M₂)
    (h₁ : ∀ (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      f (update m i (x + y)) = f (update m i x) + f (update m i y) := by aesop)
    (h₂ : ∀ (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      f (update m i (c • x)) = c • f (update m i x) := by aesop) :
    MultilinearMap R M₁ M₂ where
  toFun := f
  map_update_add' m i x y := by convert! h₁ m i x y
  map_update_smul' m i c x := by convert! h₂ m i c x

@[simp]
/-
**MultilinearMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：toFun_eq_coe : f.toFun = ⇑f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : f.toFun = ⇑f :=
  rfl

@[simp]
/-
**MultilinearMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：coe_mk (f : (forall i, M₁ i) -> M₂) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : MultilinearM
ap R M₁ M₂) = f
参数：f : (forall i, M₁ i) -> M₂；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : (∀ i, M₁ i) → M₂) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f :=
  rfl
/-
**MultilinearMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : forall i, M₁ i) 
: f x = g x
参数：h : f = g；x : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : ∀ i, M₁ i) : f x = g x :=
  DFunLike.congr_fun h x

nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : ∀ i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
/-
**MultilinearMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：coe_injective : Injective ((↑) : MultilinearMap R M₁ M₂ -> (forall i, M₁ i
) -> M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : Injective ((↑) : MultilinearMap R M₁ M₂ → (∀ i, M₁ i) → M₂) :=
  DFunLike.coe_injective

@[norm_cast]
/-
**MultilinearMap.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：coe_inj {f g : MultilinearMap R M₁ M₂} : (f : (forall i, M₁ i) -> M₂) = g 
↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_inj {f g : MultilinearMap R M₁ M₂} : (f : (∀ i, M₁ i) → M₂) = g ↔ f = g :=
  DFunLike.coe_fn_eq

@[ext]
/-
**MultilinearMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f x = f' x) : f = f'
参数：H : forall x, f x = f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f f' : MultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

@[simp]
/-
**MultilinearMap.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：mk_coe (f : MultilinearMap R M₁ M₂) (h₁ h₂) : (⟨f, h₁, h₂⟩ : MultilinearMa
p R M₁ M₂) = f
参数：f : MultilinearMap R M₁ M₂；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (f : MultilinearMap R M₁ M₂) (h₁ h₂) :
    (⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f := rfl

@[simp]
/-
**MultilinearMap.map_update_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Se
miring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁ i)] [inst_2 : AddCommMonoid M₂
] [inst_3 : (i : ι) → _root_.Module R (M₁ i)]   [inst_4 : _root_.Module R M₂] (f
 : MultilinearMap R M₁ M₂) [inst_5 : DecidableEq ι] (m : (i : ι) → M₁ i) (i : ι)
   (x y : M₁ i), f (Function.update m i (x + y)) = f (Function.update m i x) + f
 (Function.update m i y)
参数：i : ι；M₁ i；i : ι；M₁ i；f : MultilinearMap R M₁ M₂；m : (i : ι) → M₁ i；i : ι；x y
 : M₁ i；Function.update m i (x + y)；Function.update m i x；Function.update m i y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_add'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
-/
protected theorem map_update_add [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

/-- Earlier, this name was used by what is now called `MultilinearMap.map_update_smul_left`. -/
@[simp]
/-
**MultilinearMap.map_update_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Se
miring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁ i)] [inst_2 : AddCommMonoid M₂
] [inst_3 : (i : ι) → _root_.Module R (M₁ i)]   [inst_4 : _root_.Module R M₂] (f
 : MultilinearMap R M₁ M₂) [inst_5 : DecidableEq ι] (m : (i : ι) → M₁ i) (i : ι)
   (c : R) (x : M₁ i), f (Function.update m i (c • x)) = c • f (Function.update 
m i x)
参数：i : ι；M₁ i；i : ι；M₁ i；f : MultilinearMap R M₁ M₂；m : (i : ι) → M₁ i；i : ι；c :
 R；x : M₁ i；Function.update m i (c • x)；Function.update m i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_smul'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι →
 Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid
 (M₁ i)] [inst_2 : Ad…

--- 原说明 ---
Earlier, this name was used by what is now called `MultilinearMap.map_update_smu
l_left`.
-/
protected theorem map_update_smul [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x
/-
**MultilinearMap.map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_coord_zero {m : forall i, M₁ i} (i : ι) (h : m i = 0) : f m = 0
参数：i : ι；h : m i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 := by
  classical
    have : (0 : R) • (0 : M₁ i) = 0 := by simp
    rw [← update_eq_self i m, h, ← this, f.map_update_smul, zero_smul]

@[simp]
/-
**MultilinearMap.map_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_update_zero [DecidableEq ι] (m : forall i, M₁ i) (i : ι) : f (update m
 i 0) = 0
参数：m : forall i, M₁ i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem map_update_zero [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : f (update m i 0) = 0 :=
  f.map_coord_zero i (update_self i 0 m)

@[simp]
/-
**MultilinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_zero [Nonempty ι] : f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_mem_of_nonempty`：∀ (α : Type u_1) [Nonempty α], ∃ x, x ∈ Set.
univ
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
-/
theorem map_zero [Nonempty ι] : f 0 = 0 := by
  obtain ⟨i, _⟩ : ∃ i : ι, i ∈ Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (MultilinearMap R M₁ M₂) :=
  ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc], fun m i c x => by
      simp [smul_add]⟩⟩
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (MultilinearMap R M₁ M₂) :=
  ⟨⟨fun _ => 0, fun _ _ _ _ => by simp, fun _ _ c _ => by simp⟩⟩
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  zero_apply _ := rfl
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MultilinearMap R M₁ M₂) :=
  ⟨0⟩

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

section SMul

variable [DistribSMul S M₂] [SMulCommClass R S M₂]

/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (MultilinearMap R M₁ M₂) :=
  ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M₂)]⟩⟩
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply S (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

end SMul

-- The `AddMonoid` instance exists to help speedup unification
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (MultilinearMap R M₁ M₂) := fast_instance% FunLike.addMonoid
/-
**MultilinearMap.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
形式化陈述：addCommMonoid : AddCommMonoid (MultilinearMap R M₁ M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (MultilinearMap R M₁ M₂) := fast_instance%
  FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_sum := FunLike.coe_sum

@[deprecated (since := "2026-06-10")] protected alias sum_apply := _root_.sum_apply

/-- If `f` is a multilinear map, then `f.toLinearMap m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
@[simps]
/-
**MultilinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：toLinearMap [DecidableEq ι] (m : forall i, M₁ i) (i : ι) : M₁ i ->ₗ[R] M₂ 
where toFun x
参数：m : forall i, M₁ i；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a multilinear map, then `f.toLinearMap m i` is the linear map obtained
 by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate.
-/
def toLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ where
  toFun x := f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The Cartesian product of two multilinear maps, as a multilinear map. -/
@[simps]
/-
**MultilinearMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) : Multiline
arMap R M₁ (M₂ × M₃) where toFun m
参数：f : MultilinearMap R M₁ M₂；g : MultilinearMap R M₁ M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two multilinear maps, as a multilinear map.
-/
def prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) :
    MultilinearMap R M₁ (M₂ × M₃) where
  toFun m := (f m, g m)
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

/-- Combine a family of multilinear maps with the same domain and codomains `M' i` into a
multilinear map taking values in the space of functions `∀ i, M' i`. -/
@[simps]
/-
**MultilinearMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [foral
l i, Module R (M' i)] (f : forall i, MultilinearMap R M₁ (M' i)) : MultilinearMa
p R M₁ (forall i, M' i) where toFun m i
参数：M' i；M' i；f : forall i, MultilinearMap R M₁ (M' i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of multilinear maps with the same domain and codomains `M' i` i
nto a
multilinear map taking values in the space of functions `∀ i, M' i`.
-/
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, MultilinearMap R M₁ (M' i)) : MultilinearMap R M₁ (∀ i, M' i) where
  toFun m i := f i m
  map_update_add' _ _ _ _ := funext fun j => (f j).map_update_add _ _ _ _
  map_update_smul' _ _ _ _ := funext fun j => (f j).map_update_smul _ _ _ _

section

variable (R M₂ M₃)

/-- Equivalence between linear maps `M₂ →ₗ[R] M₃` and one-multilinear maps. -/
@[simps]
/-
**MultilinearMap.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：ofSubsingleton [Subsingleton ι] (i : ι) : (M₂ ->ₗ[R] M₃) ≃ MultilinearMap 
R (fun _ : ι => M₂) M₃ where toFun f
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between linear maps `M₂ →ₗ[R] M₃` and one-multilinear maps.
-/
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ MultilinearMap R (fun _ : ι ↦ M₂) M₃ where
  toFun f :=
    { toFun := fun x ↦ f (x i)
      map_update_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_update_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x ↦ f fun _ ↦ x
      map_add' := fun x y ↦ by
        simpa [update_eq_const_of_subsingleton] using! f.map_update_add 0 i x y
      map_smul' := fun c x ↦ by
        simpa [update_eq_const_of_subsingleton] using! f.map_update_smul 0 i c x }
  right_inv f := by ext x; refine congr_arg f ?_; exact (eq_const_of_subsingleton _ _).symm

variable (M₁) {M₂}

/-- The constant map is multilinear when `ι` is empty. -/
@[simps -fullyApplied]
/-
**MultilinearMap.constOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where toFun
参数：m : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant map is multilinear when `ι` is empty.
-/
def constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where
  toFun := Function.const _ m
  map_update_add' _ := isEmptyElim
  map_update_smul' _ := isEmptyElim

end

/-- Given a multilinear map `f` on `n` variables (parameterized by `Fin n`) and a subset `s` of `k`
of these variables, one gets a new multilinear map on `Fin k` by varying these variables, and fixing
the other ones equal to a given value `z`. It is denoted by `f.restr s hk z`, where `hk` is a
proof that the cardinality of `s` is `k`. The implicit identification between `Fin k` and `s` that
we use is the canonical (increasing) bijection. -/
/-
**MultilinearMap.restr** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：restr {k n : Nat} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Fin
set (Fin n)) (hk : #s = k) (z : M') : MultilinearMap R (fun _ : Fin k => M') M₂ 
where toFun v
参数：f : MultilinearMap R (fun _ : Fin n => M') M₂；s : Finset (Fin n)；hk : #s = k；
z : M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multilinear map `f` on `n` variables (parameterized by `Fin n`) and a su
bset `s` of `k`
of these variables, one gets a new multilinear map on `Fin k` by varying these v
ariables, and fixing
the other ones equal to a given value `z`. It is denoted by `f.restr s hk z`, wh
ere `hk` is a
proof that the cardinality of `s` is `k`. The implicit identification between `F
in k` and `s` that
we use is the canonical (increasing) bijection.
-/
def restr {k n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Finset (Fin n))
    (hk : #s = k) (z : M') : MultilinearMap R (fun _ : Fin k => M') M₂ where
  toFun v := f fun j => if h : j ∈ s then v ((s.orderIsoOfFin hk).symm ⟨j, h⟩) else z
  map_update_add' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]
  map_update_smul' := by
    simp [dite_comp_equiv_update (s.orderIsoOfFin hk).symm]

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly the additivity of a
multilinear map along the first variable. -/
/-
**MultilinearMap.cons_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：cons_add (f : MultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (x y
 : M 0) : f (cons (x + y) m) = f (cons x m) + f (cons y m)
参数：f : MultilinearMap R M M₂；m : forall i : Fin n, M i.succ；x y : M 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.update_cons_zero`：update_cons_zero : update (cons x p) 0 z = cons z 
p
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where
 one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly th
e additivity of a
multilinear map along the first variable.
-/
theorem cons_add (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) := by
  simp_rw [← update_cons_zero x m (x + y), f.map_update_add, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
/-
**MultilinearMap.cons_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：cons_smul (f : MultilinearMap R M M₂) (m : forall i : Fin n, M i.succ) (c 
: R) (x : M 0) : f (cons (c • x) m) = c • f (cons x m)
参数：f : MultilinearMap R M M₂；m : forall i : Fin n, M i.succ；c : R；x : M 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.update_cons_zero`：update_cons_zero : update (cons x p) 0 z = cons z 
p
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where
 one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly th
e multiplicativity
of a multilinear map along the first variable.
-/
theorem cons_smul (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (c : R) (x : M 0) :
    f (cons (c • x) m) = c • f (cons x m) := by
  simp_rw [← update_cons_zero x m (c • x), f.map_update_smul, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `snoc`, one can express directly the additivity of a
multilinear map along the first variable. -/
/-
**MultilinearMap.snoc_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：snoc_add (f : MultilinearMap R M M₂) (m : forall i : Fin n, M (castSucc i)
) (x y : M (last n)) : f (snoc m (x + y)) = f (snoc m x) + f (snoc m y)
参数：f : MultilinearMap R M M₂；m : forall i : Fin n, M (castSucc i)；x y : M (last 
n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.update_snoc_last`：update_snoc_last : update (snoc p x) (last n) z = 
snoc p z
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where
 one can build
an element of `∀ (i : Fin (n+1)), M i` using `snoc`, one can express directly th
e additivity of a
multilinear map along the first variable.
-/
theorem snoc_add (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x y : M (last n)) :
    f (snoc m (x + y)) = f (snoc m x) + f (snoc m y) := by
  simp_rw [← update_snoc_last x m (x + y), f.map_update_add, update_snoc_last]

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
/-
**MultilinearMap.snoc_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：snoc_smul (f : MultilinearMap R M M₂) (m : forall i : Fin n, M (castSucc i
)) (c : R) (x : M (last n)) : f (snoc m (c • x)) = c • f (snoc m x)
参数：f : MultilinearMap R M M₂；m : forall i : Fin n, M (castSucc i)；c : R；x : M (l
ast n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.update_snoc_last`：update_snoc_last : update (snoc p x) (last n) z = 
snoc p z
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where
 one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly th
e multiplicativity
of a multilinear map along the first variable.
-/
theorem snoc_smul (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M (castSucc i)) (c : R)
    (x : M (last n)) : f (snoc m (c • x)) = c • f (snoc m x) := by
  simp_rw [← update_snoc_last x m (c • x), f.map_update_smul, update_snoc_last]
/-
**MultilinearMap.map_insertNth_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_insertNth_add (f : MultilinearMap R M M₂) (p : Fin (n + 1)) (m : foral
l i, M (p.succAbove i)) (x y : M p) : f (p.insertNth (x + y) m) = f (p.insertNth
 x m) + f (p.insertNth y m)
参数：f : MultilinearMap R M M₂；p : Fin (n + 1)；m : forall i, M (p.succAbove i)；x y
 : M p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.update_insertNth`：update_insertNth (p : Fin (n + 1)) (x y : α p) (f 
: forall i, α (p.succAbove i)) : update (p.insertNth x f) p y = p.insertNth y f
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
-/
theorem map_insertNth_add (f : MultilinearMap R M M₂) (p : Fin (n + 1)) (m : ∀ i, M (p.succAbove i))
    (x y : M p) : f (p.insertNth (x + y) m) = f (p.insertNth x m) + f (p.insertNth y m) := by
  simpa using f.map_update_add (p.insertNth 0 m) p x y
/-
**MultilinearMap.map_insertNth_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_insertNth_smul (f : MultilinearMap R M M₂) (p : Fin (n + 1)) (m : fora
ll i, M (p.succAbove i)) (c : R) (x : M p) : f (p.insertNth (c • x) m) = c • f (
p.insertNth x m)
参数：f : MultilinearMap R M M₂；p : Fin (n + 1)；m : forall i, M (p.succAbove i)；c :
 R；x : M p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.update_insertNth`：update_insertNth (p : Fin (n + 1)) (x y : α p) (f 
: forall i, α (p.succAbove i)) : update (p.insertNth x f) p y = p.insertNth y f
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
-/
theorem map_insertNth_smul (f : MultilinearMap R M M₂) (p : Fin (n + 1))
    (m : ∀ i, M (p.succAbove i)) (c : R) (x : M p) :
    f (p.insertNth (c • x) m) = c • f (p.insertNth x m) := by
  simpa using f.map_update_smul (p.insertNth 0 m) p c x

section

variable [∀ i, AddCommMonoid (M₁' i)] [∀ i, Module R (M₁' i)]
variable [∀ i, AddCommMonoid (M₁'' i)] [∀ i, Module R (M₁'' i)]

/-- If `g` is a multilinear map and `f` is a collection of linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a multilinear map, that we call
`g.compLinearMap f`. -/
/-
**MultilinearMap.compLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：compLinearMap (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[R] M₁'
 i) : MultilinearMap R M₁ M₂ where toFun m
参数：g : MultilinearMap R M₁' M₂；f : forall i, M₁ i ->ₗ[R] M₁' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a multilinear map and `f` is a collection of linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a multilinear map, that we call
`g.compLinearMap f`.
-/
def compLinearMap (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    MultilinearMap R M₁ M₂ where
  toFun m := g fun i => f i (m i)
  map_update_add' m i x y := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_update_smul' m i c x := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]

@[simp]
/-
**MultilinearMap.compLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：compLinearMap_apply (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[
R] M₁' i) (m : forall i, M₁ i) : g.compLinearMap f m = g fun i => f i (m i)
参数：g : MultilinearMap R M₁' M₂；f : forall i, M₁ i ->ₗ[R] M₁' i；m : forall i, M₁ 
i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compLinearMap_apply (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i)
    (m : ∀ i, M₁ i) : g.compLinearMap f m = g fun i => f i (m i) :=
  rfl

/-- Composing a multilinear map twice with a linear map in each argument is
the same as composing with their composition. -/
/-
**MultilinearMap.compLinearMap_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : forall i, M₁' i -
>ₗ[R] M₁'' i) (f₂ : forall i, M₁ i ->ₗ[R] M₁' i) : (g.compLinearMap f₁).compLine
arMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i
参数：g : MultilinearMap R M₁'' M₂；f₁ : forall i, M₁' i ->ₗ[R] M₁'' i；f₂ : forall i
, M₁ i ->ₗ[R] M₁' i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a multilinear map twice with a linear map in each argument is
the same as composing with their composition.
-/
theorem compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : ∀ i, M₁' i →ₗ[R] M₁'' i)
    (f₂ : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i :=
  rfl

/-- Composing the zero multilinear map with a linear map in each argument. -/
@[simp]
/-
**MultilinearMap.zero_compLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：zero_compLinearMap (f : forall i, M₁ i ->ₗ[R] M₁' i) : (0 : MultilinearMap
 R M₁' M₂).compLinearMap f = 0
参数：f : forall i, M₁ i ->ₗ[R] M₁' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'

--- 原说明 ---
Composing the zero multilinear map with a linear map in each argument.
-/
theorem zero_compLinearMap (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0 :=
  ext fun _ => rfl

/-- Composing a multilinear map with the identity linear map in each argument. -/
@[simp]
/-
**MultilinearMap.compLinearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：compLinearMap_id (g : MultilinearMap R M₁' M₂) : (g.compLinearMap fun _ =>
 LinearMap.id) = g
参数：g : MultilinearMap R M₁' M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'

--- 原说明 ---
Composing a multilinear map with the identity linear map in each argument.
-/
theorem compLinearMap_id (g : MultilinearMap R M₁' M₂) :
    (g.compLinearMap fun _ => LinearMap.id) = g :=
  ext fun _ => rfl

/-- Composing with a family of surjective linear maps is injective. -/
/-
**MultilinearMap.compLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearM
ap`。
形式化陈述：compLinearMap_injective (f : forall i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, 
Surjective (f i)) : Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap
 f
参数：f : forall i, M₁ i ->ₗ[R] M₁' i；hf : forall i, Surjective (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MultilinearMap.ext_iff`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Type v₁}
 {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁ i)] 
[inst_2 : Ad…

--- 原说明 ---
Composing with a family of surjective linear maps is injective.
-/
theorem compLinearMap_injective (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i)) :
    Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)]
      using MultilinearMap.ext_iff.mp h fun i => surjInv (hf i) (x i)
/-
**MultilinearMap.compLinearMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：compLinearMap_inj (f : forall i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, Surjec
tive (f i)) (g₁ g₂ : MultilinearMap R M₁' M₂) : g₁.compLinearMap f = g₂.compLine
arMap f ↔ g₁ = g₂
参数：f : forall i, M₁ i ->ₗ[R] M₁' i；hf : forall i, Surjective (f i)；g₁ g₂ : Multi
linearMap R M₁' M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MultilinearMap.compLinearMap_injective`：compLinearMap_injective (f : for
all i, M₁ i ->ₗ[R] M₁' i) (hf : forall i, Surjective (f i)) : Injective fun g : 
MultilinearMap R M₁' M₂ => g…
-/
theorem compLinearMap_inj (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i))
    (g₁ g₂ : MultilinearMap R M₁' M₂) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- Composing a multilinear map with a linear equiv on each argument gives the zero map
if and only if the multilinear map is the zero map. -/
@[simp]
/-
**MultilinearMap.comp_linearEquiv_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multili
nearMap`。
形式化陈述：comp_linearEquiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : forall i, 
M₁ i ≃ₗ[R] M₁' i) : (g.compLinearMap fun i => (f i : M₁ i ->ₗ[R] M₁' i)) = 0 ↔ g
 = 0
参数：g : MultilinearMap R M₁' M₂；f : forall i, M₁ i ≃ₗ[R] M₁' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.zero_compLinearMap`：zero_compLinearMap (f : forall i, M₁ 
i ->ₗ[R] M₁' i) : (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0
· 使用定理 `MultilinearMap.compLinearMap_inj`：compLinearMap_inj (f : forall i, M₁ i 
->ₗ[R] M₁' i) (hf : forall i, Surjective (f i)) (g₁ g₂ : MultilinearMap R M₁' M₂
) : g₁.compLinearMap f…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Composing a multilinear map with a linear equiv on each argument gives the zero 
map
if and only if the multilinear map is the zero map.
-/
theorem comp_linearEquiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i ≃ₗ[R] M₁' i) :
    (g.compLinearMap fun i => (f i : M₁ i →ₗ[R] M₁' i)) = 0 ↔ g = 0 := by
  set f' := fun i => (f i : M₁ i →ₗ[R] M₁' i)
  rw [← zero_compLinearMap f', compLinearMap_inj f' fun i => (f i).surjective]


section compMultilinear

variable {β : ι → Type*}
variable {N : (i : ι) → (b : β i) → Type*}
variable [∀ i, ∀ b, AddCommMonoid (N i b)] [∀ i, ∀ b, Module R (N i b)]

/-- Composition of multilinear maps. If `g` is multilinear, and if for every `i : ι`, we have a
multilinear map `f i` with index type `β i`, then `m ↦ g (f₁ m_11 m_12 ...) (f₂ m_21 m_22 ...) ...`
is multilinear with index type `(Σ i, β i)`. -/
@[simps]
/-
**MultilinearMap.compMultilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：compMultilinearMap (g : MultilinearMap R M₁ M₂) (f : (i : ι) -> Multilinea
rMap R (N i) (M₁ i)) : MultilinearMap R (fun j : Σ i, β i => N j.fst j.snd) M₂ w
here toFun m
参数：g : MultilinearMap R M₁ M₂；f : (i : ι) -> MultilinearMap R (N i) (M₁ i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of multilinear maps. If `g` is multilinear, and if for every `i : ι`
, we have a
multilinear map `f i` with index type `β i`, then `m ↦ g (f₁ m_11 m_12 ...) (f₂ 
m_21 m_22 ...) ...`
is multilinear with index type `(Σ i, β i)`.
-/
def compMultilinearMap (g : MultilinearMap R M₁ M₂) (f : (i : ι) → MultilinearMap R (N i) (M₁ i)) :
    MultilinearMap R (fun j : Σ i, β i ↦ N j.fst j.snd) M₂ where
  toFun m := g fun i ↦ f i (Sigma.curry m i)
  map_update_add' {hDecEqSigma} := by
    classical
    simp +instances [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma,
      Sigma.curry_update, Function.apply_update (fun i ↦ f i)]
  map_update_smul' {hDecEqSigma} := by
    classical
    simp +instances [Subsingleton.elim hDecEqSigma Sigma.instDecidableEqSigma,
      Sigma.curry_update, Function.apply_update (fun i ↦ f i)]

end compMultilinear

end

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite. -/
/-
**MultilinearMap.map_piecewise_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_piecewise_add [DecidableEq ι] (m m' : forall i, M₁ i) (t : Finset ι) :
 f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m')
参数：m m' : forall i, M₁ i；t : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.piecewise_insert`：piecewise_insert [DecidableEq ι] (j : ι) [foral
l i, Decidable (i in insert j s)] : (insert j s).piecewise f g = update (s.piece
wise f g) j (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
· 使用定理 `Finset.sum_powerset_insert`：∀ {α : Type u_1} {β : Type u_2} {s : Finset 
α} {a : α} [inst : AddCommMonoid β] [inst_1 : DecidableEq α],   a ∉ s →     ∀ (f
 : Finset α → β)…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.notMem_of_mem_powerset_of_notMem`：notMem_of_mem_powerset_of_notMe
m {s t : Finset α} {a : α} (ht : t in s.powerset) (h : a ∉ s) : a ∉ t
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p

--- 原说明 ---
If one adds to a vector `m'` another vector `m`, but only for coordinates in a f
inset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along
 all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, 
given in
`map_add_univ`, although it can be useful in its own right as it does not requir
e the index set `ι`
to be finite.
-/
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') := by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [hit]
    · simp [h]
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', hit]
    · by_cases h' : j ∈ t <;> simp [m'', h, h']
  rw [A, f.map_update_add, B, C, Finset.sum_powerset_insert hit, Hrec, Hrec, add_comm (_ : M₂)]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', Finset.notMem_of_mem_powerset_of_notMem hs hit]
    · by_cases h' : j ∈ s <;> simp [m'', h, h']
  rw [this]

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
/-
**MultilinearMap.map_add_univ** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_add_univ [DecidableEq ι] [Fintype ι] (m m' : forall i, M₁ i) : f (m + 
m') = ∑ s : Finset ι, f (s.piecewise m m')
参数：m m' : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_univ`：piecewise_univ [forall i, Decidable (i in (univ :
 Finset ι))] (f g : forall i, π i) : univ.piecewise f g = f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.powerset_univ`：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.p
owerset = Finset.univ
· 使用定理 `MultilinearMap.map_piecewise_add`：map_piecewise_add [DecidableEq ι] (m m
' : forall i, M₁ i) (t : Finset ι) : f (t.piecewise (m + m') m') = ∑ s in t.powe
rset, f (s.piecewise m…

--- 原说明 ---
Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`.
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') := by
  simpa using f.map_piecewise_add m m' Finset.univ

section ApplySum

variable {α : ι → Type*} (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

open Fintype Finset

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof. Use instead
`map_sum_finset`. -/
/-
**MultilinearMap.map_sum_finset_aux** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_sum_finset_aux [DecidableEq ι] [Fintype ι] {n : Nat} (h : (∑ i, #(A i)
) = n) : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i
)
参数：h : (∑ i, #(A i)) = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用引理 `Finset.card_ne_zero`：card_ne_zero : #s != 0 ↔ s.Nonempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_le_one_iff`：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s
 -> b in s -> a = b
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `Fintype.card_piFinset`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : Decid
ableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)),   (Fintype.piFinset
 s).card = …
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Finset.one_lt_card_iff`：one_lt_card_iff : 1 < #s ↔ exists a b, a in s ∧ 
b in s ∧ a != b
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is t
he sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁
`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with resp
ect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof
. Use instead
`map_sum_finset`.
-/
theorem map_sum_finset_aux [DecidableEq ι] [Fintype ι] {n : ℕ} (h : (∑ i, #(A i)) = n) :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) := by
  let := fun i => Classical.decEq (α i)
  induction n using Nat.strong_induction_on generalizing A with | h n IH =>
  -- If one of the sets is empty, then all the sums are zero
  by_cases! Ai_empty : ∃ i, A i = ∅
  · obtain ⟨i, hi⟩ : ∃ i, ∑ j ∈ A i, g i j = 0 := Ai_empty.imp fun i hi ↦ by simp [hi]
    have hpi : piFinset A = ∅ := by simpa
    rw [f.map_coord_zero i hi, hpi, Finset.sum_empty]
  -- Otherwise, if all sets are at most singletons, then they are exactly singletons and the result
  -- is again straightforward
  by_cases! Ai_singleton : ∀ i, #(A i) ≤ 1
  · have Ai_card : ∀ i, #(A i) = 1 := by
      intro i
      have pos : #(A i) ≠ 0 := by rw [Finset.card_ne_zero]; exact Ai_empty i
      have : #(A i) ≤ 1 := Ai_singleton i
      exact le_antisymm this (Nat.succ_le_of_lt (_root_.pos_iff_ne_zero.mpr pos))
    have :
      ∀ r : ∀ i, α i, r ∈ piFinset A → (f fun i => g i (r i)) = f fun i => ∑ j ∈ A i, g i j := by
      intro r hr
      congr with i
      have : ∀ j ∈ A i, g i j = g i (r i) := by
        intro j hj
        congr
        apply Finset.card_le_one_iff.1 (Ai_singleton i) hj
        exact mem_piFinset.mp hr i
      simp only [Finset.sum_congr rfl this, Finset.sum_const, Ai_card i, one_nsmul]
    simp only [Finset.sum_congr rfl this, Ai_card, card_piFinset, prod_const_one, one_nsmul,
      Finset.sum_const]
  -- Remains the interesting case where one of the `A i`, say `A i₀`, has cardinality at least 2.
  -- We will split into two parts `B i₀` and `C i₀` of smaller cardinality, let `B i = C i = A i`
  -- for `i ≠ i₀`, apply the inductive assumption to `B` and `C`, and add up the corresponding
  -- parts to get the sum for `A`.
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 < #(A i) := Ai_singleton
  obtain ⟨j₁, j₂, _, hj₂, _⟩ : ∃ j₁ j₂, j₁ ∈ A i₀ ∧ j₂ ∈ A i₀ ∧ j₁ ≠ j₂ :=
    Finset.one_lt_card_iff.1 hi₀
  let B := Function.update A i₀ (A i₀ \ {j₂})
  let C := Function.update A i₀ {j₂}
  have B_subset_A : ∀ i, B i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [B, Finset.sdiff_subset, update_self]
    · simp only [B, hi, update_of_ne, Ne, not_false_iff, Finset.Subset.refl]
  have C_subset_A : ∀ i, C i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [C, hj₂, Finset.singleton_subset_iff, update_self]
    · simp only [C, hi, update_of_ne, Ne, not_false_iff, Finset.Subset.refl]
  -- split the sum at `i₀` as the sum over `B i₀` plus the sum over `C i₀`, to use additivity.
  have A_eq_BC :
    (fun i => ∑ j ∈ A i, g i j) =
      Function.update (fun i => ∑ j ∈ A i, g i j) i₀
        ((∑ j ∈ B i₀, g i₀ j) + ∑ j ∈ C i₀, g i₀ j) := by
    ext i
    by_cases hi : i = i₀
    · rw [hi, update_self]
      have : A i₀ = B i₀ ∪ C i₀ := by
        simp only [B, C, Function.update_self, Finset.sdiff_union_self_eq_union]
        symm
        simp only [hj₂, Finset.singleton_subset_iff, Finset.union_eq_left]
      rw [this]
      refine Finset.sum_union <| Finset.disjoint_right.2 fun j hj => ?_
      have : j = j₂ := by
        simpa [C] using hj
      rw [this]
      simp only [B, Finset.mem_sdiff, not_true, not_false_iff, Finset.mem_singleton,
        update_self, and_false]
    · simp [hi]
  have Beq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ B i₀, g i₀ j) = fun i =>
      ∑ j ∈ B i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_self]
    · simp only [B, hi, update_of_ne, Ne, not_false_iff]
  have Ceq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ C i₀, g i₀ j) = fun i =>
      ∑ j ∈ C i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_self]
    · simp only [C, hi, update_of_ne, Ne, not_false_iff]
  -- Express the inductive assumption for `B`
  have Brec : (f fun i => ∑ j ∈ B i, g i j) = ∑ r ∈ piFinset B, f fun i => g i (r i) := by
    have : ∑ i, #(B i) < ∑ i, #(A i) := by
      refine sum_lt_sum (fun i _ => card_le_card (B_subset_A i)) ⟨i₀, mem_univ _, ?_⟩
      have : {j₂} ⊆ A i₀ := by simp [hj₂]
      simp only [B, Finset.card_sdiff_of_subset this, Function.update_self, Finset.card_singleton]
      exact Nat.pred_lt (ne_of_gt (lt_trans Nat.zero_lt_one hi₀))
    rw [h] at this
    exact IH _ this B rfl
  -- Express the inductive assumption for `C`
  have Crec : (f fun i => ∑ j ∈ C i, g i j) = ∑ r ∈ piFinset C, f fun i => g i (r i) := by
    have : (∑ i, #(C i)) < ∑ i, #(A i) :=
      Finset.sum_lt_sum (fun i _ => Finset.card_le_card (C_subset_A i))
        ⟨i₀, Finset.mem_univ _, by simp [C, hi₀]⟩
    rw [h] at this
    exact IH _ this C rfl
  have D : Disjoint (piFinset B) (piFinset C) :=
    haveI : Disjoint (B i₀) (C i₀) := by simp [B, C]
    piFinset_disjoint_of_disjoint B C this
  have pi_BC : piFinset A = piFinset B ∪ piFinset C := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases hri₀ : r i₀ = j₂
      · apply Finset.mem_union_right
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ C i₀ := by simp [C, hri₀]
          rwa [hi]
        · simp [C, hi, mem_piFinset.1 hr i]
      · apply Finset.mem_union_left
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ B i₀ := by simp [B, hri₀, mem_piFinset.1 hr i₀]
          rwa [hi]
        · simp [B, hi, mem_piFinset.1 hr i]
    · exact
        Finset.union_subset (piFinset_subset _ _ fun i => B_subset_A i)
          (piFinset_subset _ _ fun i => C_subset_A i)
  rw [A_eq_BC]
  simp only [MultilinearMap.map_update_add, Beq, Ceq, Brec, Crec, pi_BC]
  rw [← Finset.sum_union D]

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
/-
**MultilinearMap.map_sum_finset** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_sum_finset [DecidableEq ι] [Fintype ι] : (f fun i => ∑ j in A i, g i j
) = ∑ r in piFinset A, f fun i => g i (r i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_sum_finset_aux`：map_sum_finset_aux [DecidableEq ι] [F
intype ι] {n : Nat} (h : (∑ i, #(A i)) = n) : (f fun i => ∑ j in A i, g i j) = ∑
 r in piFinset A, f fun…

--- 原说明 ---
If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is t
he sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁
`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with resp
ect to each
coordinate.
-/
theorem map_sum_finset [DecidableEq ι] [Fintype ι] :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) :=
  f.map_sum_finset_aux _ _ rfl

/-- If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
/-
**MultilinearMap.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_sum [DecidableEq ι] [Fintype ι] [forall i, Fintype (α i)] : (f fun i =
> ∑ j, g i j) = ∑ r : forall i, α i, f fun i => g i (r i)
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] [Fintype ι
] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)

--- 原说明 ---
If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This foll
ows from
multilinearity by expanding successively with respect to each coordinate.
-/
theorem map_sum [DecidableEq ι] [Fintype ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.map_sum_finset g fun _ => Finset.univ
/-
**MultilinearMap.map_update_sum** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α -
> M₁ i) (m : forall i, M₁ i) : f (update m i (∑ a in t, g a)) = ∑ a in t, f (upd
ate m i (g a))
参数：t : Finset α；i : ι；g : α -> M₁ i；m : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.map_update_zero`：map_update_zero [DecidableEq ι] (m : for
all i, M₁ i) (i : ι) : f (update m i 0) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
-/
theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M₁ i)
    (m : ∀ i, M₁ i) : f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) := by
  classical
    induction t using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, ih]

end ApplySum

/-- Restrict the codomain of a multilinear map to a submodule.

This is the multilinear version of `LinearMap.codRestrict`. -/
@[simps]
/-
**MultilinearMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : forall 
v, f v in p) : MultilinearMap R M₁ p where toFun v
参数：f : MultilinearMap R M₁ M₂；p : Submodule R M₂；h : forall v, f v in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a multilinear map to a submodule.

This is the multilinear version of `LinearMap.codRestrict`.
-/
def codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    MultilinearMap R M₁ p where
  toFun v := ⟨f v, h v⟩
  map_update_add' _ _ _ _ := Subtype.ext <| MultilinearMap.map_update_add _ _ _ _ _
  map_update_smul' _ _ _ _ := Subtype.ext <| MultilinearMap.map_update_smul _ _ _ _ _

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
/-
**MultilinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ wher
e toFun
参数：f : MultilinearMap A M₁ M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…

--- 原说明 ---
Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algeb
ra over `R`
and their actions on all involved modules agree with the action of `R` on `A`.
-/
def restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ where
  toFun := f
  map_update_add' := f.map_update_add
  map_update_smul' m i := (f.toLinearMap m i).map_smul_of_tower

@[simp]
/-
**MultilinearMap.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：coe_restrictScalars (f : MultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) 
= f
参数：f : MultilinearMap A M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : MultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

section

variable {ι₁ ι₂ ι₃ : Type*}

/-- Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `Finsupp.domCongr`, noting that here the permutation applies to the
domain of the domain. -/
@[simps apply]
/-
**MultilinearMap.domDomCongr** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) : M
ultilinearMap R (fun _ : ι₂ => M₂) M₃ where toFun v
参数：σ : ι₁ ≃ ι₂；m : MultilinearMap R (fun _ : ι₁ => M₂) M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `Finsupp.domCongr`, noting that here the permutation 
applies to the
domain of the domain.
-/
def domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun v := m fun i => v (σ i)
  map_update_add' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_add]
  map_update_smul' v i a b := by
    let := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_update_smul]
/-
**MultilinearMap.domDomCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：domDomCongr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃) (m : MultilinearMap R (fun
 _ : ι₁ => M₂) M₃) : m.domDomCongr (σ₁.trans σ₂) = (m.domDomCongr σ₁).domDomCong
r σ₂
参数：σ₁ : ι₁ ≃ ι₂；σ₂ : ι₂ ≃ ι₃；m : MultilinearMap R (fun _ : ι₁ => M₂) M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem domDomCongr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₁.trans σ₂) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
/-
**MultilinearMap.domDomCongr_mul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：domDomCongr_mul (σ₁ : Equiv.Perm ι₁) (σ₂ : Equiv.Perm ι₁) (m : Multilinear
Map R (fun _ : ι₁ => M₂) M₃) : m.domDomCongr (σ₂ * σ₁) = (m.domDomCongr σ₁).domD
omCongr σ₂
参数：σ₁ : Equiv.Perm ι₁；σ₂ : Equiv.Perm ι₁；m : MultilinearMap R (fun _ : ι₁ => M₂)
 M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domDomCongr_mul (σ₁ : Equiv.Perm ι₁) (σ₂ : Equiv.Perm ι₁)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₂ * σ₁) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

/-- `MultilinearMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
/-
**MultilinearMap.domDomCongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domDomCongrEquiv (σ : ι₁ ≃ ι₂) : MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+
 MultilinearMap R (fun _ : ι₂ => M₂) M₃ where toFun
参数：σ : ι₁ ≃ ι₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`MultilinearMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation.
-/
def domDomCongrEquiv (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]

/-- The results of applying `domDomCongr` to two maps are equal if
and only if those maps are. -/
@[simp]
/-
**MultilinearMap.domDomCongr_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：domDomCongr_eq_iff (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun _ : ι₁ => M₂
) M₃) : f.domDomCongr σ = g.domDomCongr σ ↔ f = g
参数：σ : ι₁ ≃ ι₂；f g : MultilinearMap R (fun _ : ι₁ => M₂) M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.apply_eq_iff_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M]
 [inst_1 : Add N] (e : M ≃+ N) {x y : M}, e x = e y ↔ x = y

--- 原说明 ---
The results of applying `domDomCongr` to two maps are equal if
and only if those maps are.
-/
theorem domDomCongr_eq_iff (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun _ => M₂) M₃).apply_eq_iff_eq

end

/-! If `{a // P a}` is a subtype of `ι` and if we fix an element `z` of `(i : {a // ¬ P a}) → M₁ i`,
then a multilinear map on `M₁` defines a multilinear map on the restriction of `M₁` to
`{a // P a}`, by fixing the arguments out of `{a // P a}` equal to the values of `z`. -/

/-
**MultilinearMap.domDomRestrict_aux** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：domDomRestrict_aux {ι} [DecidableEq ι] (P : ι -> Prop) [DecidablePred P] {
M₁ : ι -> Type*} [DecidableEq {a // P a}] (x : (i : {a // P a}) -> M₁ i) (z : (i
 : {a // ¬ P a}) -> M₁ i) (i : {a : ι // P a}) (c : M₁ i) : (fun j => if h : P j
 then Function.update x i c ⟨j, h⟩ else z ⟨j, h⟩) = Function.update (fun j => if
 h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c
参数：P : ι -> Prop；x : (i : {a // P a}) -> M₁ i；z : (i : {a // ¬ P a}) -> M₁ i；i :
 {a : ι // P a}；c : M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `{a // P a}` is a subtype of `ι` and if we fix an element `z` of `(i : {a // 
¬ P a}) → M₁ i`,
then a multilinear map on `M₁` defines a multilinear map on the restriction of `
M₁` to
`{a // P a}`, by fixing the arguments out of `{a // P a}` equal to the values of
 `z`.
-/
lemma domDomRestrict_aux {ι} [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {M₁ : ι → Type*}
    [DecidableEq {a // P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // P a})
    (c : M₁ i) : (fun j ↦ if h : P j then Function.update x i c ⟨j, h⟩ else z ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by grind
/-
**MultilinearMap.domDomRestrict_aux_right** 是 Mathlib 中的一个引理，位于命名空间 `Multilinear
Map`。
形式化陈述：domDomRestrict_aux_right {ι} [DecidableEq ι] (P : ι -> Prop) [DecidablePre
d P] {M₁ : ι -> Type*} [DecidableEq {a // ¬ P a}] (x : (i : {a // P a}) -> M₁ i)
 (z : (i : {a // ¬ P a}) -> M₁ i) (i : {a : ι // ¬ P a}) (c : M₁ i) : (fun j => 
if h : P j then x ⟨j, h⟩ else Function.update z i c ⟨j, h⟩) = Function.update (f
un j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c
参数：P : ι -> Prop；x : (i : {a // P a}) -> M₁ i；z : (i : {a // ¬ P a}) -> M₁ i；i :
 {a : ι // ¬ P a}；c : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_not`：∀ {p : Prop} {α : Sort u_1} [hn : Decidable ¬p] [h : Decidable
 p] (x : ¬p → α) (y : ¬¬p → α),   dite (¬p) x y = dite p (fun h => y ⋯) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `MultilinearMap.domDomRestrict_aux`：domDomRestrict_aux {ι} [DecidableEq ι
] (P : ι -> Prop) [DecidablePred P] {M₁ : ι -> Type*} [DecidableEq {a // P a}] (
x : (i : {a // P a}) ->…
-/
lemma domDomRestrict_aux_right {ι} [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {M₁ : ι → Type*}
    [DecidableEq {a // ¬ P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // ¬ P a})
    (c : M₁ i) : (fun j ↦ if h : P j then x ⟨j, h⟩ else Function.update z i c ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  simpa only [dite_not] using domDomRestrict_aux _ z (fun j ↦ x ⟨j.1, not_not.mp j.2⟩) i c

/-- Given a multilinear map `f` on `(i : ι) → M i`, a (decidable) predicate `P` on `ι` and
an element `z` of `(i : {a // ¬ P a}) → M₁ i`, construct a multilinear map on
`(i : {a // P a}) → M₁ i)` whose value at `x` is `f` evaluated at the vector with `i`th coordinate
`x i` if `P i` and `z i` otherwise.

The naming is similar to `MultilinearMap.domDomCongr`: here we are applying the restriction to the
domain of the domain.

For a linear map version, see `MultilinearMap.domDomRestrictₗ`.
-/
/-
**MultilinearMap.domDomRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [DecidablePred
 P] (z : (i : {a : ι // ¬ P a}) -> M₁ i) : MultilinearMap R (fun (i : {a : ι // 
P a}) => M₁ i) M₂ where toFun x
参数：f : MultilinearMap R M₁ M₂；P : ι -> Prop；z : (i : {a : ι // ¬ P a}) -> M₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multilinear map `f` on `(i : ι) → M i`, a (decidable) predicate `P` on `
ι` and
an element `z` of `(i : {a // ¬ P a}) → M₁ i`, construct a multilinear map on
`(i : {a // P a}) → M₁ i)` whose value at `x` is `f` evaluated at the vector wit
h `i`th coordinate
`x i` if `P i` and `z i` otherwise.

The naming is similar to `MultilinearMap.domDomCongr`: here we are applying the 
restriction to the
domain of the domain.

For a linear map version, see `MultilinearMap.domDomRestrictₗ`.
-/
def domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P]
    (z : (i : {a : ι // ¬ P a}) → M₁ i) :
    MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂ where
  toFun x := f (fun j ↦ if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_update_add' x i a b := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_add]
  map_update_smul' z i c a := by
    classical
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_update_smul]

@[simp]
/-
**MultilinearMap.domDomRestrict_apply** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`
。
形式化陈述：domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [Decidab
lePred P] (x : (i : {a // P a}) -> M₁ i) (z : (i : {a // ¬ P a}) -> M₁ i) : f.do
mDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
参数：f : MultilinearMap R M₁ M₂；P : ι -> Prop；x : (i : {a // P a}) -> M₁ i；z : (i 
: {a // ¬ P a}) -> M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι → Prop)
    [DecidablePred P] (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) :
    f.domDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) := rfl

-- TODO: Should add a ref here when available.
/-- The "derivative" of a multilinear map, as a linear map from `(i : ι) → M₁ i` to `M₂`.
For continuous multilinear maps, this will indeed be the derivative. -/
/-
**MultilinearMap.linearDeriv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂) (x : 
(i : ι) -> M₁ i) : ((i : ι) -> M₁ i) ->ₗ[R] M₂
参数：f : MultilinearMap R M₁ M₂；x : (i : ι) -> M₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "derivative" of a multilinear map, as a linear map from `(i : ι) → M₁ i` to 
`M₂`.
For continuous multilinear maps, this will indeed be the derivative.
-/
def linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x : (i : ι) → M₁ i) : ((i : ι) → M₁ i) →ₗ[R] M₂ :=
  ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]
/-
**MultilinearMap.linearDeriv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
 (x y : (i : ι) -> M₁ i) : f.linearDeriv x y = ∑ i, f (update x i (y i))
参数：f : MultilinearMap R M₁ M₂；x y : (i : ι) -> M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MultilinearMap.toLinearMap_apply`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι 
→ Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoi
d (M₁ i)] [inst_2 : Ad…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

end Semiring

end MultilinearMap

namespace LinearMap

variable [Semiring R]
variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M₁' i)]
  [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄] [AddCommMonoid M']
variable [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)]
  [Module R M₂] [Module R M₃] [Module R M₄] [Module R M']

/-- Composing a multilinear map with a linear map gives again a multilinear map. -/
/-
**LinearMap.compMultilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compMultilinearMap (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : Multi
linearMap R M₁ M₃ where toFun
参数：g : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a multilinear map with a linear map gives again a multilinear map.
-/
def compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : MultilinearMap R M₁ M₃ where
  toFun := g ∘ f
  map_update_add' m i x y := by simp
  map_update_smul' m i c x := by simp

@[simp]
/-
**LinearMap.coe_compMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_compMultilinearMap (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : ⇑
(g.compMultilinearMap f) = g ∘ f
参数：g : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    ⇑(g.compMultilinearMap f) = g ∘ f :=
  rfl

@[simp]
/-
**LinearMap.compMultilinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compMultilinearMap_apply (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (
m : forall i, M₁ i) : g.compMultilinearMap f m = g (f m)
参数：g : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂；m : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compMultilinearMap_apply (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) :
    g.compMultilinearMap f m = g (f m) :=
  rfl

@[simp]
/-
**LinearMap.id_compMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_compMultilinearMap (f : MultilinearMap R M₁ M₂) : (id : M₂ ->ₗ[R] M₂).c
ompMultilinearMap f = f
参数：f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_compMultilinearMap (f : MultilinearMap R M₁ M₂) :
    (id : M₂ →ₗ[R] M₂).compMultilinearMap f = f := rfl
/-
**LinearMap.comp_compMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_compMultilinearMap (g : M₃ ->ₗ[R] M₄) (g' : M₂ ->ₗ[R] M₃) (f : Multil
inearMap R M₁ M₂) : (g.comp g').compMultilinearMap f = g.compMultilinearMap (g'.
compMultilinearMap f)
参数：g : M₃ ->ₗ[R] M₄；g' : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_compMultilinearMap (g : M₃ →ₗ[R] M₄) (g' : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    (g.comp g').compMultilinearMap f = g.compMultilinearMap (g'.compMultilinearMap f) := rfl

/-- The two types of composition are associative. -/
/-
**LinearMap.compMultilinearMap_compLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p`。
形式化陈述：compMultilinearMap_compLinearMap (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R 
M₁ M₂) (f' : forall i, M₁' i ->ₗ[R] M₁ i) : g.compMultilinearMap (f.compLinearMa
p f') = (g.compMultilinearMap f).compLinearMap f'
参数：g : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂；f' : forall i, M₁' i ->ₗ[R] M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two types of composition are associative.
-/
theorem compMultilinearMap_compLinearMap
    (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (f' : ∀ i, M₁' i →ₗ[R] M₁ i) :
    g.compMultilinearMap (f.compLinearMap f') = (g.compMultilinearMap f).compLinearMap f' := rfl

@[simp]
/-
**LinearMap.compMultilinearMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compMultilinearMap_zero (g : M₂ ->ₗ[R] M₃) : g.compMultilinearMap (0 : Mul
tilinearMap R M₁ M₂) = 0
参数：g : M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
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
-/
theorem compMultilinearMap_zero (g : M₂ →ₗ[R] M₃) :
    g.compMultilinearMap (0 : MultilinearMap R M₁ M₂) = 0 :=
  MultilinearMap.ext fun _ => map_zero g

@[simp]
/-
**LinearMap.zero_compMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：zero_compMultilinearMap (f : MultilinearMap R M₁ M₂) : (0 : M₂ ->ₗ[R] M₃).
compMultilinearMap f = 0
参数：f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_compMultilinearMap (f : MultilinearMap R M₁ M₂) :
    (0 : M₂ →ₗ[R] M₃).compMultilinearMap f = 0 := rfl

@[simp]
/-
**LinearMap.compMultilinearMap_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compMultilinearMap_add (g : M₂ ->ₗ[R] M₃) (f₁ f₂ : MultilinearMap R M₁ M₂)
 : g.compMultilinearMap (f₁ + f₂) = g.compMultilinearMap f₁ + g.compMultilinearM
ap f₂
参数：g : M₂ ->ₗ[R] M₃；f₁ f₂ : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem compMultilinearMap_add (g : M₂ →ₗ[R] M₃) (f₁ f₂ : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (f₁ + f₂) = g.compMultilinearMap f₁ + g.compMultilinearMap f₂ :=
  MultilinearMap.ext fun _ => map_add g _ _

@[simp]
/-
**LinearMap.add_compMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：add_compMultilinearMap (g₁ g₂ : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
 : (g₁ + g₂).compMultilinearMap f = g₁.compMultilinearMap f + g₂.compMultilinear
Map f
参数：g₁ g₂ : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_compMultilinearMap (g₁ g₂ : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    (g₁ + g₂).compMultilinearMap f = g₁.compMultilinearMap f + g₂.compMultilinearMap f := rfl

@[simp]
/-
**LinearMap.compMultilinearMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compMultilinearMap_smul [DistribSMul S M₂] [DistribSMul S M₃] [SMulCommCla
ss R S M₂] [SMulCommClass R S M₃] [CompatibleSMul M₂ M₃ S R] (g : M₂ ->ₗ[R] M₃) 
(s : S) (f : MultilinearMap R M₁ M₂) : g.compMultilinearMap (s • f) = s • g.comp
MultilinearMap f
参数：g : M₂ ->ₗ[R] M₃；s : S；f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem compMultilinearMap_smul [DistribSMul S M₂] [DistribSMul S M₃]
    [SMulCommClass R S M₂] [SMulCommClass R S M₃] [CompatibleSMul M₂ M₃ S R]
    (g : M₂ →ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    g.compMultilinearMap (s • f) = s • g.compMultilinearMap f :=
  MultilinearMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]
/-
**LinearMap.smul_compMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：smul_compMultilinearMap [Monoid S] [DistribMulAction S M₃] [SMulCommClass 
R S M₃] (g : M₂ ->ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) : (s • g).compMu
ltilinearMap f = s • g.compMultilinearMap f
参数：g : M₂ ->ₗ[R] M₃；s : S；f : MultilinearMap R M₁ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_compMultilinearMap [Monoid S] [DistribMulAction S M₃] [SMulCommClass R S M₃]
    (g : M₂ →ₗ[R] M₃) (s : S) (f : MultilinearMap R M₁ M₂) :
    (s • g).compMultilinearMap f = s • g.compMultilinearMap f := rfl

/-- The multilinear version of `LinearMap.subtype_comp_codRestrict` -/
@[simp]
/-
**LinearMap.subtype_compMultilinearMap_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：subtype_compMultilinearMap_codRestrict (f : MultilinearMap R M₁ M₂) (p : S
ubmodule R M₂) (h) : p.subtype.compMultilinearMap (f.codRestrict p h) = f
参数：f : MultilinearMap R M₁ M₂；p : Submodule R M₂；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multilinear version of `LinearMap.subtype_comp_codRestrict`
-/
theorem subtype_compMultilinearMap_codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂)
    (h) : p.subtype.compMultilinearMap (f.codRestrict p h) = f :=
  rfl

/-- The multilinear version of `LinearMap.comp_codRestrict` -/
@[simp]
/-
**LinearMap.compMultilinearMap_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：compMultilinearMap_codRestrict (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R M₁
 M₂) (p : Submodule R M₃) (h) : (g.codRestrict p h).compMultilinearMap f = (g.co
mpMultilinearMap f).codRestrict p fun v => h (f v)
参数：g : M₂ ->ₗ[R] M₃；f : MultilinearMap R M₁ M₂；p : Submodule R M₃；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multilinear version of `LinearMap.comp_codRestrict`
-/
theorem compMultilinearMap_codRestrict (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
    (p : Submodule R M₃) (h) :
    (g.codRestrict p h).compMultilinearMap f =
      (g.compMultilinearMap f).codRestrict p fun v => h (f v) :=
  rfl

variable {ι₁ ι₂ : Type*}

@[simp]
/-
**LinearMap.compMultilinearMap_domDomCongr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：compMultilinearMap_domDomCongr (σ : ι₁ ≃ ι₂) (g : M₂ ->ₗ[R] M₃) (f : Multi
linearMap R (fun _ : ι₁ => M') M₂) : (g.compMultilinearMap f).domDomCongr σ = g.
compMultilinearMap (f.domDomCongr σ)
参数：σ : ι₁ ≃ ι₂；g : M₂ ->ₗ[R] M₃；f : MultilinearMap R (fun _ : ι₁ => M') M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compMultilinearMap_domDomCongr (σ : ι₁ ≃ ι₂) (g : M₂ →ₗ[R] M₃)
    (f : MultilinearMap R (fun _ : ι₁ => M') M₂) :
    (g.compMultilinearMap f).domDomCongr σ = g.compMultilinearMap (f.domDomCongr σ) := by
  ext
  simp [MultilinearMap.domDomCongr]

end LinearMap

namespace MultilinearMap

section Semiring

variable [Semiring R] [(i : ι) → AddCommMonoid (M₁ i)] [(i : ι) → Module R (M₁ i)]
  [AddCommMonoid M₂] [Module R M₂]

/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [DistribMulAction S M₂] [SMulCommClass R S M₂] :
    DistribMulAction S (MultilinearMap R M₁ M₂) := fast_instance% FunLike.distribMulAction

section Module

variable [Semiring S] [Module S M₂] [SMulCommClass R S M₂]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of multilinear maps over an algebra over `R` is a module over `R`, for
 the pointwise
addition and scalar multiplication.
-/
instance : Module S (MultilinearMap R M₁ M₂) := fast_instance%
  FunLike.module
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.IsTorsionFree S M₂] : Module.IsTorsionFree S (MultilinearMap R M₁ M₂) :=
  coe_injective.moduleIsTorsionFree _ FunLike.coe_smul

variable [AddCommMonoid M₃] [Module S M₃] [Module R M₃] [SMulCommClass R S M₃]

variable (S) in
/-- `LinearMap.compMultilinearMap` as an `S`-linear map. -/
@[simps]
/-
**MultilinearMap._root_.LinearMap.compMultilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `
MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.compMultilinearMap` as an `S`-linear map.
-/
def _root_.LinearMap.compMultilinearMapₗ [LinearMap.CompatibleSMul M₂ M₃ S R] (g : M₂ →ₗ[R] M₃) :
    MultilinearMap R M₁ M₂ →ₗ[S] MultilinearMap R M₁ M₃ where
  toFun := g.compMultilinearMap
  map_add' := g.compMultilinearMap_add
  map_smul' := g.compMultilinearMap_smul

variable (S) in
/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `LinearMap.compMultilinearMap` as an `S`-linear equivalence,
and the multilinear version of `LinearEquiv.congrRight`. -/
@[simps! apply symm_apply]
/-
**MultilinearMap._root_.LinearEquiv.multilinearMapCongrRight** 是 Mathlib 中的一个定义，
位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `LinearMap.compMultilinearMap` as an `S`-linear equivalence,
and the multilinear version of `LinearEquiv.congrRight`.
-/
def _root_.LinearEquiv.multilinearMapCongrRight
    [LinearMap.CompatibleSMul M₂ M₃ S R] [LinearMap.CompatibleSMul M₃ M₂ S R] (g : M₂ ≃ₗ[R] M₃) :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R M₁ M₃ where
  __ := g.toLinearMap.compMultilinearMapₗ S
  invFun := g.symm.toLinearMap.compMultilinearMapₗ S
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

variable (R S M₁ M₂ M₃)

section OfSubsingleton

/-- Linear equivalence between linear maps `M₂ →ₗ[R] M₃`
and one-multilinear maps `MultilinearMap R (fun _ : ι ↦ M₂) M₃`. -/
@[simps +simpRhs]
/-
**MultilinearMap.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：ofSubsingleton [Subsingleton ι] (i : ι) : (M₂ ->ₗ[R] M₃) ≃ MultilinearMap 
R (fun _ : ι => M₂) M₃ where toFun f
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between linear maps `M₂ →ₗ[R] M₃`
and one-multilinear maps `MultilinearMap R (fun _ : ι ↦ M₂) M₃`.
-/
def ofSubsingletonₗ [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ₗ[S] MultilinearMap R (fun _ : ι ↦ M₂) M₃ :=
  { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

end OfSubsingleton

/-- The dependent version of `MultilinearMap.domDomCongrLinearEquiv`. -/
@[simps apply symm_apply]
/-
**MultilinearMap.domDomCongrLinearEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearM
ap`。
形式化陈述：domDomCongrLinearEquiv' {ι' : Type*} (σ : ι ≃ ι') : MultilinearMap R M₁ M₂
 ≃ₗ[S] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where toFun f
参数：σ : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The dependent version of `MultilinearMap.domDomCongrLinearEquiv`.
-/
def domDomCongrLinearEquiv' {ι' : Type*} (σ : ι ≃ ι') :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where
  toFun f :=
    { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_update_add' := fun m i => by
        let := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        let := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_symm_update, f.map_update_smul] }
  invFun f :=
    { toFun := f ∘ σ.piCongrLeft' M₁
      map_update_add' := fun m i => by
        let := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_update, f.map_update_add]
      map_update_smul' := fun m i c => by
        let := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_update, f.map_update_smul] }
  map_add' f₁ f₂ := by
    ext
    simp only [Function.comp, coe_mk, add_apply]
  map_smul' c f := by
    ext
    simp only [Function.comp, coe_mk, smul_apply, RingHom.id_apply]
  left_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.symm_apply_apply]
  right_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.apply_symm_apply]

/-- The space of constant maps is equivalent to the space of maps that are multilinear with respect
to an empty family. -/
@[simps]
/-
**MultilinearMap.constLinearEquivOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Multilinea
rMap`。
形式化陈述：constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[S] MultilinearMap R M₁ M₂ wh
ere toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of constant maps is equivalent to the space of maps that are multiline
ar with respect
to an empty family.
-/
def constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[S] MultilinearMap R M₁ M₂ where
  toFun := MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  right_inv f := ext fun _ => MultilinearMap.congr_arg f <| Subsingleton.elim _ _

/-- `MultilinearMap.domDomCongr` as a `LinearEquiv`. -/
@[simps apply symm_apply]
/-
**MultilinearMap.domDomCongrLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMa
p`。
形式化陈述：domDomCongrLinearEquiv {ι₁ ι₂} (σ : ι₁ ≃ ι₂) : MultilinearMap R (fun _ : ι
₁ => M₂) M₃ ≃ₗ[S] MultilinearMap R (fun _ : ι₂ => M₂) M₃
参数：σ : ι₁ ≃ ι₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MultilinearMap.domDomCongr` as a `LinearEquiv`.
-/
def domDomCongrLinearEquiv {ι₁ ι₂} (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃ₗ[S] MultilinearMap R (fun _ : ι₂ => M₂) M₃ :=
  { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }

end Module

end Semiring

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

section
variable [Π i, AddCommMonoid (M₁' i)] [Π i, Module R (M₁' i)]

/-- Given a predicate `P`, one may associate to a multilinear map `f` a multilinear map
from the elements satisfying `P` to the multilinear maps on elements not satisfying `P`.
In other words, splitting the variables into two subsets one gets a multilinear map into
multilinear maps.
This is a linear map version of the function `MultilinearMap.domDomRestrict`. -/
/-
**MultilinearMap.domDomRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι -> Prop) [DecidablePred
 P] (z : (i : {a : ι // ¬ P a}) -> M₁ i) : MultilinearMap R (fun (i : {a : ι // 
P a}) => M₁ i) M₂ where toFun x
参数：f : MultilinearMap R M₁ M₂；P : ι -> Prop；z : (i : {a : ι // ¬ P a}) -> M₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `P`, one may associate to a multilinear map `f` a multilinear 
map
from the elements satisfying `P` to the multilinear maps on elements not satisfy
ing `P`.
In other words, splitting the variables into two subsets one gets a multilinear 
map into
multilinear maps.
This is a linear map version of the function `MultilinearMap.domDomRestrict`.
-/
def domDomRestrictₗ (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P] :
    MultilinearMap R (fun (i : {a : ι // ¬ P a}) => M₁ i)
      (MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂) where
  toFun := fun z ↦ domDomRestrict f P z
  map_update_add' := by
    intro h m i x y
    classical
    ext v
    simp [domDomRestrict_aux_right]
  map_update_smul' := by
    intro h m i c x
    classical
    ext v
    simp [domDomRestrict_aux_right]
/-
**MultilinearMap.iteratedFDeriv_aux** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：iteratedFDeriv_aux {ι} {M₁ : ι -> Type*} {α : Type*} [DecidableEq α] (s : 
Set ι) [DecidableEq { x // x in s }] (e : α ≃ s) (m : α -> ((i : ι) -> M₁ i)) (a
 : α) (z : (i : ι) -> M₁ i) : (fun i => update m a z (e.symm i) i) = (fun i => u
pdate (fun j => m (e.symm j) j) (e a) (z (e a)) i)
参数：s : Set ι；e : α ≃ s；m : α -> ((i : ι) -> M₁ i)；a : α；z : (i : ι) -> M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma iteratedFDeriv_aux {ι} {M₁ : ι → Type*} {α : Type*} [DecidableEq α]
    (s : Set ι) [DecidableEq { x // x ∈ s }] (e : α ≃ s)
    (m : α → ((i : ι) → M₁ i)) (a : α) (z : (i : ι) → M₁ i) :
    (fun i ↦ update m a z (e.symm i) i) =
      (fun i ↦ update (fun j ↦ m (e.symm j) j) (e a) (z (e a)) i) := by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_self, update_self]
  · rw [update_of_ne hne.symm, update_of_ne fun h ↦ (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]

/-- One of the components of the iterated derivative of a multilinear map. Given a bijection `e`
between a type `α` (typically `Fin k`) and a subset `s` of `ι`, this component is a multilinear map
of `k` vectors `v₁, ..., vₖ`, mapping them to `f (x₁, (v_{e.symm 2})₂, x₃, ...)`, where at
indices `i` in `s` one uses the `i`-th coordinate of the vector `v_{e.symm i}` and otherwise one
uses the `i`-th coordinate of a reference vector `x`.
This is multilinear in the components of `x` outside of `s`, and in the `v_j`. -/
/-
**MultilinearMap.iteratedFDerivComponent** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearM
ap`。
形式化陈述：iteratedFDerivComponent {α : Type*} (f : MultilinearMap R M₁ M₂) {s : Set 
ι} (e : α ≃ s) [DecidablePred (· in s)] : MultilinearMap R (fun (i : {a : ι // a
 ∉ s}) => M₁ i) (MultilinearMap R (fun (_ : α) => (forall i, M₁ i)) M₂) where to
Fun
参数：f : MultilinearMap R M₁ M₂；e : α ≃ s；· in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
One of the components of the iterated derivative of a multilinear map. Given a b
ijection `e`
between a type `α` (typically `Fin k`) and a subset `s` of `ι`, this component i
s a multilinear map
of `k` vectors `v₁, ..., vₖ`, mapping them to `f (x₁, (v_{e.symm 2})₂, x₃, ...)`
, where at
indices `i` in `s` one uses the `i`-th coordinate of the vector `v_{e.symm i}` a
nd otherwise one
uses the `i`-th coordinate of a reference vector `x`.
This is multilinear in the components of `x` outside of `s`, and in the `v_j`.
-/
noncomputable def iteratedFDerivComponent {α : Type*}
    (f : MultilinearMap R M₁ M₂) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)] :
    MultilinearMap R (fun (i : {a : ι // a ∉ s}) ↦ M₁ i)
      (MultilinearMap R (fun (_ : α) ↦ (∀ i, M₁ i)) M₂) where
  toFun := fun z ↦
    { toFun := fun v ↦ domDomRestrictₗ f (fun i ↦ i ∈ s) z (fun i ↦ v (e.symm i) i)
      map_update_add' := by classical simp [iteratedFDeriv_aux]
      map_update_smul' := by classical simp [iteratedFDeriv_aux] }
  map_update_add' := by intros; ext; simp
  map_update_smul' := by intros; ext; simp

open scoped Classical in
/-- The `k`-th iterated derivative of a multilinear map `f` at the point `x`. It is a multilinear
map of `k` vectors `v₁, ..., vₖ` (with the same type as `x`), mapping them
to `∑ f (x₁, (v_{i₁})₂, x₃, ...)`, where at each index `j` one uses either `xⱼ` or one
of the `(vᵢ)ⱼ`, and each `vᵢ` has to be used exactly once.
The sum is parameterized by the embeddings of `Fin k` in the index type `ι` (or, equivalently,
by the subsets `s` of `ι` of cardinality `k` and then the bijections between `Fin k` and `s`).

For the continuous version, see `ContinuousMultilinearMap.iteratedFDeriv`. -/
/-
**MultilinearMap.iteratedFDeriv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：{R : Type uR} →   {ι : Type uι} →     {M₁ : ι → Type v₁} →       {M₂ : Typ
e v₂} →         [inst : CommSemiring R] →           [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] →             [inst_2 : AddCommMonoid M₂] →               [inst_3 
: (i : ι) → _root_.Module R (M₁ i)] →                 [inst_4 : _root_.Module R 
M₂] →                   [Fintype ι] →                     MultilinearMap R M₁ M₂
 → (k : ℕ) → ((i : ι) → M₁ i) → MultilinearMap R (fun x => (i : ι) → M₁ i) M₂
参数：i : ι；M₁ i；i : ι；M₁ i；k : ℕ；(i : ι) → M₁ i；fun x => (i : ι) → M₁ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`-th iterated derivative of a multilinear map `f` at the point `x`. It is 
a multilinear
map of `k` vectors `v₁, ..., vₖ` (with the same type as `x`), mapping them
to `∑ f (x₁, (v_{i₁})₂, x₃, ...)`, where at each index `j` one uses either `xⱼ` 
or one
of the `(vᵢ)ⱼ`, and each `vᵢ` has to be used exactly once.
The sum is parameterized by the embeddings of `Fin k` in the index type `ι` (or,
 equivalently,
by the subsets `s` of `ι` of cardinality `k` and then the bijections between `Fi
n k` and `s`).

For the continuous version, see `ContinuousMultilinearMap.iteratedFDeriv`.
-/
protected noncomputable def iteratedFDeriv [Fintype ι]
    (f : MultilinearMap R M₁ M₂) (k : ℕ) (x : (i : ι) → M₁ i) :
    MultilinearMap R (fun (_ : Fin k) ↦ (∀ i, M₁ i)) M₂ :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (fun i ↦ x i)

/-- If `f` is a collection of linear maps, then the construction `MultilinearMap.compLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g`. -/
/-
**MultilinearMap.compLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：compLinearMap (g : MultilinearMap R M₁' M₂) (f : forall i, M₁ i ->ₗ[R] M₁'
 i) : MultilinearMap R M₁ M₂ where toFun m
参数：g : MultilinearMap R M₁' M₂；f : forall i, M₁ i ->ₗ[R] M₁' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a collection of linear maps, then the construction `MultilinearMap.com
pLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g`.
-/
@[simps] def compLinearMapₗ (f : Π (i : ι), M₁ i →ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂ where
  toFun := fun g ↦ g.compLinearMap f
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- An isomorphism of multilinear maps given an isomorphism between their domains.

This is `MultilinearMap.compLinearMap` as a linear equivalence,
and the multilinear version of `LinearEquiv.congrLeft`. -/
@[simps! apply symm_apply]
/-
**MultilinearMap._root_.LinearEquiv.multilinearMapCongrLeft** 是 Mathlib 中的一个定义，位
于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of multilinear maps given an isomorphism between their domains.

This is `MultilinearMap.compLinearMap` as a linear equivalence,
and the multilinear version of `LinearEquiv.congrLeft`.
-/
def _root_.LinearEquiv.multilinearMapCongrLeft (e : Π (i : ι), M₁ i ≃ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) ≃ₗ[R] MultilinearMap R M₁ M₂ where
  __ := compLinearMapₗ (e · |>.toLinearMap)
  invFun := compLinearMapₗ (e · |>.symm.toLinearMap)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- If `f` is a collection of linear maps, then the construction `MultilinearMap.compLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g` and multilinear in
`f₁, ..., fₙ`. -/
/-
**MultilinearMap.compLinearMapMultilinear** 是 Mathlib 中的一个定义，位于命名空间 `Multilinear
Map`。
形式化陈述：{R : Type uR} →   {ι : Type uι} →     {M₁ : ι → Type v₁} →       {M₁' : ι 
→ Type v₁'} →         {M₂ : Type v₂} →           [inst : CommSemiring R] →      
       [inst_1 : (i : ι) → AddCommMonoid (M₁ i)] →               [inst_2 : AddCo
mmMonoid M₂] →                 [inst_3 : (i : ι) → _root_.Module R (M₁ i)] →    
               [inst_4 : _root_.Module R M₂] →                     [inst_5 : (i 
: ι) → AddCommMonoid (M₁' i)] →                       [inst_6 : (i : ι) → _root_
.Module R (M₁' i)] →                         MultilinearMap R (fun i => M₁ i →ₗ[
R] M₁' i)                           (MultilinearMap R M₁' M₂ →ₗ[R] MultilinearMa
p R M₁ M₂)
参数：i : ι；M₁ i；i : ι；M₁ i；i : ι；M₁' i；i : ι；M₁' i；fun i => M₁ i →ₗ[R] M₁' i；Multi
linearMap R M₁' M₂ →ₗ[R] MultilinearMap R M₁ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a collection of linear maps, then the construction `MultilinearMap.com
pLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g` and mu
ltilinear in
`f₁, ..., fₙ`.
-/
@[simps] def compLinearMapMultilinear :
    @MultilinearMap R ι (fun i ↦ M₁ i →ₗ[R] M₁' i)
      ((MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂) _ _ _
        (fun _ ↦ LinearMap.module) _ where
  toFun := MultilinearMap.compLinearMapₗ
  map_update_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <| x j) + g fun j ↦ update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert! g.map_update_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) with j j j
    · exact Function.apply_update c f i (f₁ + f₂) j
    · exact Function.apply_update c f i f₁ j
    · exact Function.apply_update c f i f₂ j
  map_update_smul' := by
    intro _ f i a f₀
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert! g.map_update_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) with j j j
    · exact Function.apply_update c f i (a • f₀) j
    · exact Function.apply_update c f i f₀ j

/--
Let `M₁ᵢ` and `M₁ᵢ'` be two families of `R`-modules and `M₂` an `R`-module.
Let us denote `Π i, M₁ᵢ` and `Π i, M₁ᵢ'` by `M` and `M'` respectively.
If `g` is a multilinear map `M' → M₂`, then `g` can be reinterpreted as a multilinear
map from `Π i, M₁ᵢ ⟶ M₁ᵢ'` to `M ⟶ M₂` via `(fᵢ) ↦ v ↦ g(fᵢ vᵢ)`.
-/
/-
**MultilinearMap.piLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：{R : Type uR} →   {ι : Type uι} →     {M₁ : ι → Type v₁} →       {M₁' : ι 
→ Type v₁'} →         {M₂ : Type v₂} →           [inst : CommSemiring R] →      
       [inst_1 : (i : ι) → AddCommMonoid (M₁ i)] →               [inst_2 : AddCo
mmMonoid M₂] →                 [inst_3 : (i : ι) → _root_.Module R (M₁ i)] →    
               [inst_4 : _root_.Module R M₂] →                     [inst_5 : (i 
: ι) → AddCommMonoid (M₁' i)] →                       [inst_6 : (i : ι) → _root_
.Module R (M₁' i)] →                         MultilinearMap R M₁' M₂ →ₗ[R]      
                     MultilinearMap R (fun i => M₁ i →ₗ[R] M₁' i) (MultilinearMa
p R M₁ M₂)
参数：i : ι；M₁ i；i : ι；M₁ i；i : ι；M₁' i；i : ι；M₁' i；fun i => M₁ i →ₗ[R] M₁' i；Multi
linearMap R M₁ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M₁ᵢ` and `M₁ᵢ'` be two families of `R`-modules and `M₂` an `R`-module.
Let us denote `Π i, M₁ᵢ` and `Π i, M₁ᵢ'` by `M` and `M'` respectively.
If `g` is a multilinear map `M' → M₂`, then `g` can be reinterpreted as a multil
inear
map from `Π i, M₁ᵢ ⟶ M₁ᵢ'` to `M ⟶ M₂` via `(fᵢ) ↦ v ↦ g(fᵢ vᵢ)`.
-/
@[simps!] def piLinearMap :
    MultilinearMap R M₁' M₂ →ₗ[R]
    MultilinearMap R (fun i ↦ M₁ i →ₗ[R] M₁' i) (MultilinearMap R M₁ M₂) where
  toFun g := (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by simp
  map_smul' := by simp

end

/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `∏ i ∈ s, c i`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
/-
**MultilinearMap.map_piecewise_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_piecewise_smul [DecidableEq ι] (c : ι -> R) (m : forall i, M₁ i) (s : 
Finset ι) : f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m
参数：c : ι -> R；m : forall i, M₁ i；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `Finset.piecewise_insert`：piecewise_insert [DecidableEq ι] (j : ι) [foral
l i, Decidable (i in insert j s)] : (insert j s).piecewise f g = update (s.piece
wise f g) j (…
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
If one multiplies by `c i` the coordinates in a finset `s`, then the image under
 a multilinear
map is multiplied by `∏ i ∈ s, c i`. This is mainly an auxiliary statement to pr
ove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right
 as it does not
require the index set `ι` to be finite.
-/
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i ∈ s, c i) • f m := by
  refine s.induction_on (by simp) ?_
  intro j s j_notMem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_notMem_s]
    · simp [h]
  rw [s.piecewise_insert, f.map_update_smul, A, Hrec]
  simp [j_notMem_s, mul_smul]

/-- Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`. -/
/-
**MultilinearMap.map_smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_smul_univ [Fintype ι] (c : ι -> R) (m : forall i, M₁ i) : (f fun i => 
c i • m i) = (∏ i, c i) • f m
参数：c : ι -> R；m : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_univ`：piecewise_univ [forall i, Decidable (i in (univ :
 Finset ι))] (f g : forall i, π i) : univ.piecewise f g = f
· 使用定理 `MultilinearMap.map_piecewise_smul`：map_piecewise_smul [DecidableEq ι] (c
 : ι -> R) (m : forall i, M₁ i) (s : Finset ι) : f (s.piecewise (fun i => c i • 
m i) m) = (∏ i in s, c …

--- 原说明 ---
Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`.
-/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m := by
  classical simpa using map_piecewise_smul f c m Finset.univ

@[simp]
/-
**MultilinearMap.map_update_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`
。
形式化陈述：map_update_smul_left [DecidableEq ι] [Fintype ι] (m : forall i, M₁ i) (i :
 ι) (c : R) (x : M₁ i) : f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (
update m i x)
参数：m : forall i, M₁ i；i : ι；c : R；x : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_piecewise_smul`：map_piecewise_smul [DecidableEq ι] (c
 : ι -> R) (m : forall i, M₁ i) (s : Finset ι) : f (s.piecewise (fun i => c i • 
m i) m) = (∏ i in s, c …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.update_smul`：update_smul [forall i, SMul M (α i)] [DecidableEq 
ι] (c : M) (f₁ : forall i, α i) (i : ι) (x₁ : α i) : update (c • f₁) i (c • x₁) 
= c • upda…
· 使用引理 `Finset.piecewise_erase_univ`：piecewise_erase_univ [DecidableEq ι] (i : ι
) (f g : forall i, π i) : (Finset.univ.erase i).piecewise f g = Function.update 
f i (g i)
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_idem`：update_idem {α} [DecidableEq α] {β : α -> Sort*} {
a : α} (v w : β a) (f : forall a, β a) : update (update f a v) a w = update f a 
w
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem map_update_smul_left [DecidableEq ι] [Fintype ι]
    (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (update m i x) := by
  have : f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i ∈ Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this

/-- If two `R`-multilinear maps from `R` are equal on 1, then they are equal.

This is the multilinear version of `LinearMap.ext_ring`. -/
@[ext]
/-
**MultilinearMap.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：ext_ring [Finite ι] ⦃f g : MultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (f
un _ => 1) = g (fun _ => 1)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two `R`-multilinear maps from `R` are equal on 1, then they are equal.

This is the multilinear version of `LinearMap.ext_ring`.
-/
theorem ext_ring [Finite ι] ⦃f g : MultilinearMap R (fun _ : ι => R) M₂⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g := by
  ext x
  obtain ⟨_⟩ := nonempty_fintype ι
  have hf := f.map_smul_univ x (fun _ ↦ 1)
  have hg := g.map_smul_univ x (fun _ ↦ 1)
  simp_all

section

variable (R ι)
variable (A : Type*) [CommSemiring A] [Algebra R A] [Fintype ι]

/-- Given an `R`-algebra `A`, `mkPiAlgebra` is the multilinear map on `A^ι` associating
to `m` the product of all the `m i`.

See also `MultilinearMap.mkPiAlgebraFin` for a version that works with a non-commutative
algebra `A` but requires `ι = Fin n`. -/
/-
**MultilinearMap.mkPiAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：(R : Type uR) →   (ι : Type uι) →     [inst : CommSemiring R] →       (A :
 Type u_1) →         [inst_1 : CommSemiring A] → [inst_2 : Algebra R A] → [Finty
pe ι] → MultilinearMap R (fun x => A) A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `A`, `mkPiAlgebra` is the multilinear map on `A^ι` associat
ing
to `m` the product of all the `m i`.

See also `MultilinearMap.mkPiAlgebraFin` for a version that works with a non-com
mutative
algebra `A` but requires `ι = Fin n`.
-/
protected def mkPiAlgebra : MultilinearMap R (fun _ : ι => A) A where
  toFun m := ∏ i, m i
  map_update_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_update_smul' m i c x := by simp [Finset.prod_update_of_mem]

variable {R A ι}

@[simp]
/-
**MultilinearMap.mkPiAlgebra_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：mkPiAlgebra_apply (m : ι -> A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i,
 m i
参数：m : ι -> A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkPiAlgebra_apply (m : ι → A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl

end

section

variable (R n)
variable (A : Type*) [Semiring A] [Algebra R A]

/-- Given an `R`-algebra `A`, `mkPiAlgebraFin` is the multilinear map on `A^n` associating
to `m` the product of all the `m i`.

See also `MultilinearMap.mkPiAlgebra` for a version that assumes `[CommSemiring A]` but works
for `A^ι` with any finite type `ι`. -/
/-
**MultilinearMap.mkPiAlgebraFin** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：(R : Type uR) →   (n : ℕ) →     [inst : CommSemiring R] →       (A : Type 
u_1) → [inst_1 : Semiring A] → [inst_2 : Algebra R A] → MultilinearMap R (fun x 
=> A) A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `A`, `mkPiAlgebraFin` is the multilinear map on `A^n` assoc
iating
to `m` the product of all the `m i`.

See also `MultilinearMap.mkPiAlgebra` for a version that assumes `[CommSemiring 
A]` but works
for `A^ι` with any finite type `ι`.
-/
protected def mkPiAlgebraFin : MultilinearMap R (fun _ : Fin n => A) A :=
  MultilinearMap.mk' (fun m ↦ (List.ofFn m).prod)
    (fun m i x y ↦ by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul,
        mul_add, add_mul])
    (fun m i c x ↦ by
      simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set])

variable {R A n}

@[simp]
/-
**MultilinearMap.mkPiAlgebraFin_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`
。
形式化陈述：mkPiAlgebraFin_apply (m : Fin n -> A) : MultilinearMap.mkPiAlgebraFin R n 
A m = (List.ofFn m).prod
参数：m : Fin n -> A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    MultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl
/-
**MultilinearMap.mkPiAlgebraFin_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：mkPiAlgebraFin_apply_const (a : A) : (MultilinearMap.mkPiAlgebraFin R n A 
fun _ => a) = a ^ n
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkPiAlgebraFin_apply_const (a : A) :
    (MultilinearMap.mkPiAlgebraFin R n A fun _ => a) = a ^ n := by simp

end

/-- Given an `R`-multilinear map `f` taking values in `R`, `f.smulRight z` is the map
sending `m` to `f m • z`. -/
/-
**MultilinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂
参数：f : MultilinearMap R M₁ R；z : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-multilinear map `f` taking values in `R`, `f.smulRight z` is the ma
p
sending `m` to `f m • z`.
-/
def smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂ :=
  (LinearMap.smulRight LinearMap.id z).compMultilinearMap f

@[simp]
/-
**MultilinearMap.smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：smulRight_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : forall i, M₁ i) 
: f.smulRight z m = f m • z
参数：f : MultilinearMap R M₁ R；z : M₂；m : forall i, M₁ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRight_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : ∀ i, M₁ i) :
    f.smulRight z m = f m • z :=
  rfl

variable (R ι)

/-- The canonical multilinear map on `R^ι` when `ι` is finite, associating to `m` the product of
all the `m i` (multiplied by a fixed reference element `z` in the target module). See also
`mkPiAlgebra` for a more general version. -/
/-
**MultilinearMap.mkPiRing** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：(R : Type uR) →   (ι : Type uι) →     {M₂ : Type v₂} →       [inst : CommS
emiring R] →         [inst_1 : AddCommMonoid M₂] →           [inst_2 : _root_.Mo
dule R M₂] → [Fintype ι] → M₂ → MultilinearMap R (fun x => R) M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical multilinear map on `R^ι` when `ι` is finite, associating to `m` th
e product of
all the `m i` (multiplied by a fixed reference element `z` in the target module)
. See also
`mkPiAlgebra` for a more general version.
-/
protected def mkPiRing [Fintype ι] (z : M₂) : MultilinearMap R (fun _ : ι => R) M₂ :=
  (MultilinearMap.mkPiAlgebra R ι R).smulRight z

variable {R ι}

@[simp]
/-
**MultilinearMap.mkPiRing_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：mkPiRing_apply [Fintype ι] (z : M₂) (m : ι -> R) : (MultilinearMap.mkPiRin
g R ι z : (ι -> R) -> M₂) m = (∏ i, m i) • z
参数：z : M₂；m : ι -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkPiRing_apply [Fintype ι] (z : M₂) (m : ι → R) :
    (MultilinearMap.mkPiRing R ι z : (ι → R) → M₂) m = (∏ i, m i) • z :=
  rfl
/-
**MultilinearMap.mkPiRing_apply_one_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：mkPiRing_apply_one_eq_self [Fintype ι] (f : MultilinearMap R (fun _ : ι =>
 R) M₂) : MultilinearMap.mkPiRing R ι (f fun _ => 1) = f
参数：f : MultilinearMap R (fun _ : ι => R) M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext_ring`：ext_ring [Finite ι] ⦃f g : MultilinearMap R (fu
n _ : ι => R) M₂⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkPiRing_apply_one_eq_self [Fintype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) :
    MultilinearMap.mkPiRing R ι (f fun _ => 1) = f := by
  ext
  simp
/-
**MultilinearMap.mkPiRing_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} : MultilinearMap.mkPiRing R ι z₁ 
= MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
    MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · simp [h]
/-
**MultilinearMap.mkPiRing_zero** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：mkPiRing_zero [Fintype ι] : MultilinearMap.mkPiRing R ι (0 : M₂) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext_ring`：ext_ring [Finite ι] ⦃f g : MultilinearMap R (fu
n _ : ι => R) M₂⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.mkPiRing_apply`：mkPiRing_apply [Fintype ι] (z : M₂) (m : 
ι -> R) : (MultilinearMap.mkPiRing R ι z : (ι -> R) -> M₂) m = (∏ i, m i) • z
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
-/
theorem mkPiRing_zero [Fintype ι] : MultilinearMap.mkPiRing R ι (0 : M₂) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, zero_apply]
/-
**MultilinearMap.mkPiRing_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`
。
形式化陈述：mkPiRing_eq_zero_iff [Fintype ι] (z : M₂) : MultilinearMap.mkPiRing R ι z 
= 0 ↔ z = 0
参数：z : M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.mkPiRing_zero`：mkPiRing_zero [Fintype ι] : MultilinearMap
.mkPiRing R ι (0 : M₂) = 0
· 使用定理 `MultilinearMap.mkPiRing_eq_iff`：mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂}
 : MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mkPiRing_eq_zero_iff [Fintype ι] (z : M₂) : MultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero, mkPiRing_eq_iff]

end CommSemiring

section RangeAddCommGroup

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f g : MultilinearMap R M₁ M₂)

/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (MultilinearMap R M₁ M₂) :=
  ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (MultilinearMap R M₁ M₂) :=
  ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [MultilinearMap.map_update_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [MultilinearMap.map_update_smul, smul_sub]⟩⟩
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
/-
**MultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (MultilinearMap R M₁ M₂) := fast_instance% FunLike.addCommGroup

end RangeAddCommGroup

section AddCommGroup

variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

@[simp]
/-
**MultilinearMap.map_update_neg** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_update_neg [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x : M₁ i) : f
 (update m i (-x)) = -f (update m i x)
参数：m : forall i, M₁ i；i : ι；x : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem map_update_neg [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x : M₁ i) :
    f (update m i (-x)) = -f (update m i x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← MultilinearMap.map_update_add, neg_add_cancel, f.map_coord_zero i (update_self i 0 m)]

@[simp]
/-
**MultilinearMap.map_update_sub** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_update_sub [DecidableEq ι] (m : forall i, M₁ i) (i : ι) (x y : M₁ i) :
 f (update m i (x - y)) = f (update m i x) - f (update m i y)
参数：m : forall i, M₁ i；i : ι；x y : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MultilinearMap.map_update_add`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → T
ype v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (
M₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.map_update_neg`：map_update_neg [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x : M₁ i) : f (update m i (-x)) = -f (update m i x)
-/
theorem map_update_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, MultilinearMap.map_update_add, map_update_neg]
/-
**MultilinearMap.map_update** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：map_update [DecidableEq ι] (x : (i : ι) -> M₁ i) (i : ι) (v : M₁ i) : f (u
pdate x i v) = f x - f (update x i (x i - v))
参数：x : (i : ι) -> M₁ i；i : ι；v : M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.map_update_sub`：map_update_sub [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f 
(update m i y)
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
lemma map_update [DecidableEq ι] (x : (i : ι) → M₁ i) (i : ι) (v : M₁ i) :
    f (update x i v) = f x - f (update x i (x i - v)) := by
  rw [map_update_sub, update_eq_self, sub_sub_cancel]
/-
**MultilinearMap.map_sub_map_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap
`。
形式化陈述：map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) -> M₁ i) (s : Finset 
ι) : f a - f (s.piecewise b a) = ∑ i in s, f (fun j => if j in s -> j < i then a
 j else if i = j then a j - b j else b j)
参数：a b : (i : ι) -> M₁ i；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_min`：induction_on_min [DecidableEq α] {motive : Fins
et α -> Prop} (s : Finset α) (empty : motive ∅) (insert : forall a s, (forall x 
in s, a < x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `Finset.piecewise_insert`：piecewise_insert [DecidableEq ι] (j : ι) [foral
l i, Decidable (i in insert j s)] : (insert j s).piecewise f g = update (s.piece
wise f g) j (…
· 使用引理 `MultilinearMap.map_update`：map_update [DecidableEq ι] (x : (i : ι) -> M₁
 i) (i : ι) (v : M₁ i) : f (update x i v) = f x - f (update x i (x i - v))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
（共 32 条，此处仅展示前 30 条）
-/
lemma map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) → M₁ i) (s : Finset ι) :
    f a - f (s.piecewise b a) =
    ∑ i ∈ s, f (fun j ↦ if j ∈ s → j < i then a j else if i = j then a j - b j else b j) := by
  induction s using induction_on_min with
  | empty => rw [Finset.piecewise_empty, sum_empty, sub_self]
  | insert k s hk ih => ?_
  rw [Finset.piecewise_insert, map_update, ← sub_add, ih,
      add_comm, sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  · congr; ext i; split_ifs with h₁ h₂
    · rw [update_of_ne, Finset.piecewise_eq_of_notMem]
      · exact fun h ↦ (hk i h).not_gt (h₁ <| .inr h)
      · exact fun h ↦ (h₁ <| .inl h).ne h
    · cases h₂
      rw [update_self, s.piecewise_eq_of_notMem _ _ (lt_irrefl _ <| hk k ·)]
    · push Not at h₁
      rw [update_of_ne (Ne.symm h₂), s.piecewise_eq_of_mem _ _ (h₁.1.resolve_left <| Ne.symm h₂)]
  · apply sum_congr rfl
    grind

/-- This calculates the differences between the values of a multilinear map at
two arguments that differ on a finset `s` of `ι`. It requires a
linear order on `ι` in order to express the result. -/
/-
**MultilinearMap.map_piecewise_sub_map_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `Mult
ilinearMap`。
形式化陈述：map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) -> M₁ i) 
(s : Finset ι) : f (s.piecewise a v) - f (s.piecewise b v) = ∑ i in s, f fun j =
> if j in s then if j < i then a j else if j = i then a j - b j else b j else v 
j
参数：a b v : (i : ι) -> M₁ i；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.piecewise_idem_right`：piecewise_idem_right (f g₁ g₂ : forall a, π
 a) : s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂
· 使用引理 `MultilinearMap.map_sub_map_piecewise`：map_sub_map_piecewise [LinearOrder
 ι] (a b : (i : ι) -> M₁ i) (s : Finset ι) : f a - f (s.piecewise b a) = ∑ i in 
s, f (fun j => if j in s -…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MultilinearMap.congr_arg`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Type v
₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁ i)
] [inst_2 : Ad…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i

--- 原说明 ---
This calculates the differences between the values of a multilinear map at
two arguments that differ on a finset `s` of `ι`. It requires a
linear order on `ι` in order to express the result.
-/
lemma map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) → M₁ i) (s : Finset ι) :
    f (s.piecewise a v) - f (s.piecewise b v) = ∑ i ∈ s, f
      fun j ↦ if j ∈ s then if j < i then a j else if j = i then a j - b j else b j else v j := by
  rw [← s.piecewise_idem_right b a, map_sub_map_piecewise]
  refine Finset.sum_congr rfl fun i hi ↦ congr_arg f <| funext fun j ↦ ?_
  by_cases hjs : j ∈ s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ ↦ hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classical.not_imp.mpr ⟨hjs, hji⟩), if_neg hji]
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl, if_pos rfl, s.piecewise_eq_of_mem _ _ hi]
    · rw [if_neg hij, if_neg hij.symm]
  · rw [if_neg hjs, if_pos fun h ↦ (hjs h).elim, s.piecewise_eq_of_notMem _ _ hjs]

open Finset in
/-
**MultilinearMap.map_add_eq_map_add_linearDeriv_add** 是 Mathlib 中的一个引理，位于命名空间 `M
ultilinearMap`。
形式化陈述：map_add_eq_map_add_linearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i :
 ι) -> M₁ i) : f (x + h) = f x + f.linearDeriv x h + ∑ s with 2 <= #s, f (s.piec
ewise h x)
参数：x h : (i : ι) -> M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MultilinearMap.map_add_univ`：map_add_univ [DecidableEq ι] [Fintype ι] (m
 m' : forall i, M₁ i) : f (m + m') = ∑ s : Finset ι, f (s.piecewise m m')
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.powerset_univ`：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.p
owerset = Finset.univ
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Finset.pairwise_disjoint_powersetCard`：pairwise_disjoint_powersetCard (s
 : Finset α) : Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j
)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.powersetCard_zero`：powersetCard_zero (s : Finset α) : s.powersetC
ard 0 = {∅}
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `Finset.powersetCard_one`：powersetCard_one (s : Finset α) : s.powersetCar
d 1 = s.map ⟨_, Finset.singleton_injective⟩
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用引理 `Finset.piecewise_singleton`：piecewise_singleton [DecidableEq ι] (i : ι) 
: piecewise {i} f g = update g i (f i)
· 使用引理 `MultilinearMap.linearDeriv_apply`：linearDeriv_apply [DecidableEq ι] [Fin
type ι] (f : MultilinearMap R M₁ M₂) (x y : (i : ι) -> M₁ i) : f.linearDeriv x y
 = ∑ i, f (update x i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_add_eq_map_add_linearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i : ι) → M₁ i) :
    f (x + h) = f x + f.linearDeriv x h + ∑ s with 2 ≤ #s, f (s.piecewise h x) := by
  rw [add_comm, map_add_univ, ← Finset.powerset_univ,
      ← sum_filter_add_sum_filter_not _ (2 ≤ #·)]
  simp_rw [not_le, Nat.lt_succ_iff, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
    powersetCard_zero, powersetCard_one, sum_singleton, Finset.piecewise_empty, sum_map,
    Function.Embedding.coeFn_mk, Finset.piecewise_singleton, linearDeriv_apply, add_comm]

open Finset in
/-- This expresses the difference between the values of a multilinear map
at two points "close to `x`" in terms of the "derivative" of the multilinear map at `x`
and of "second-order" terms. -/
/-
**MultilinearMap.map_add_sub_map_add_sub_linearDeriv** 是 Mathlib 中的一个引理，位于命名空间 `
MultilinearMap`。
形式化陈述：map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : 
(i : ι) -> M₁ i) : f (x + h) - f (x + h') - f.linearDeriv x (h - h') = ∑ s with 
2 <= #s, (f (s.piecewise h x) - f (s.piecewise h' x))
参数：x h h' : (i : ι) -> M₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MultilinearMap.map_add_eq_map_add_linearDeriv_add`：map_add_eq_map_add_li
nearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i : ι) -> M₁ i) : f (x + h) = 
f x + f.linearDeriv x h + ∑ s with 2 <=…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This expresses the difference between the values of a multilinear map
at two points "close to `x`" in terms of the "derivative" of the multilinear map
 at `x`
and of "second-order" terms.
-/
lemma map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) → M₁ i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') =
    ∑ s with 2 ≤ #s, (f (s.piecewise h x) - f (s.piecewise h' x)) := by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← map_sub, add_sub_cancel_left, sum_sub_distrib]

end AddCommGroup

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂]

/-- When `ι` is finite, multilinear maps on `R^ι` with values in `M₂` are in bijection with `M₂`,
as such a multilinear map is completely determined by its value on the constant vector made of ones.
We register this bijection as a linear equivalence in `MultilinearMap.piRingEquiv`. -/
/-
**MultilinearMap.piRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：{R : Type uR} →   {ι : Type uι} →     {M₂ : Type v₂} →       [inst : CommS
emiring R] →         [inst_1 : AddCommMonoid M₂] →           [inst_2 : _root_.Mo
dule R M₂] → [Fintype ι] → M₂ ≃ₗ[R] MultilinearMap R (fun x => R) M₂
参数：fun x => R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.mkPiRing_apply_one_eq_self`：mkPiRing_apply_one_eq_self [F
intype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) : MultilinearMap.mkPiRing R
 ι (f fun _ => 1) = f

--- 原说明 ---
When `ι` is finite, multilinear maps on `R^ι` with values in `M₂` are in bijecti
on with `M₂`,
as such a multilinear map is completely determined by its value on the constant 
vector made of ones.
We register this bijection as a linear equivalence in `MultilinearMap.piRingEqui
v`.
-/
protected def piRingEquiv [Fintype ι] : M₂ ≃ₗ[R] MultilinearMap R (fun _ : ι => R) M₂ where
  toFun z := MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp
  map_smul' c z := by
    ext
    simp
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self

end CommSemiring

section Submodule

variable [Ring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M₁ i)] [Module R M'] [Module R M₂]

/-- The pushforward of an indexed collection of submodule `p i ⊆ M₁ i` by `f : M₁ → M₂`.

Note that this is not a submodule - it is not closed under addition. -/
/-
**MultilinearMap.map** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : forall i, Submodule R (
M₁ i)) : SubMulAction R M₂ where carrier
参数：f : MultilinearMap R M₁ M₂；p : forall i, Submodule R (M₁ i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of an indexed collection of submodule `p i ⊆ M₁ i` by `f : M₁ → 
M₂`.

Note that this is not a submodule - it is not closed under addition.
-/
def map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    SubMulAction R M₂ where
  carrier := f '' { v | ∀ i, v i ∈ p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    let := Classical.decEq ι
    refine ⟨update x i (c • x i), fun j => if hij : j = i then ?_ else ?_, hf ▸ ?_⟩
    · rw [hij, update_self]
      exact (p i).smul_mem _ (hx i)
    · rw [update_of_ne hij]
      exact hx j
    · rw [f.map_update_smul, update_eq_self]

/-- The map is always nonempty. This lemma is needed to apply `SubMulAction.zero_mem`. -/
/-
**MultilinearMap.map_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : forall i, Subm
odule R (M₁ i)) : (map f p : Set M₂).Nonempty
参数：f : MultilinearMap R M₁ M₂；p : forall i, Submodule R (M₁ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p

--- 原说明 ---
The map is always nonempty. This lemma is needed to apply `SubMulAction.zero_mem
`.
-/
theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    (map f p : Set M₂).Nonempty :=
  ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

/-- The range of a multilinear map, closed under scalar multiplication. -/
/-
**MultilinearMap.range** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂
参数：f : MultilinearMap R M₁ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a multilinear map, closed under scalar multiplication.
-/
def range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂ :=
  f.map fun _ => ⊤

end Submodule

end MultilinearMap

