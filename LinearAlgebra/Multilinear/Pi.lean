/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Interactions between (dependent) functions and multilinear maps

## Main definitions

* `MultilinearMap.pi_ext`, a multilinear version of `LinearMap.pi_ext`
* `MultilinearMap.piFamily`, which satisfies `piFamily f x p = f p (fun i => x i (p i))`.

  This is useful because all the intermediate results are bundled:

  - `MultilinearMap.piFamily f` is a `MultilinearMap` operating on functions `x`.
  - `MultilinearMap.piFamilyₗ` is a `LinearMap`, linear in the family of multilinear maps `f`.
-/

@[expose] public section

universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {S : Type uS} {R : Type uR}

namespace MultilinearMap

section Semiring

variable {M : ∀ i, κ i → Type uM} {N : Type uN}
variable [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [AddCommMonoid N]
variable [∀ i k, Module R (M i k)] [Module R N]

/-- Two multilinear maps from finite families are equal if they agree on the generators.

This is a multilinear version of `LinearMap.pi_ext`. -/
@[ext]
/-
**MultilinearMap.pi_ext** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：pi_ext [Finite ι] [forall i, Finite (κ i)] [forall i, DecidableEq (κ i)] ⦃
f g : MultilinearMap R (fun i => Π j : κ i, M i j) N⦄ (h : forall p : Π i, κ i, 
f.compLinearMap (fun i => LinearMap.single R _ (p i)) = g.compLinearMap (fun i =
> LinearMap.single R _ (p i))) : f = g
参数：κ i；κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] [Fintype ι
] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Two multilinear maps from finite families are equal if they agree on the generat
ors.

This is a multilinear version of `LinearMap.pi_ext`.
-/
theorem pi_ext [Finite ι] [∀ i, Finite (κ i)] [∀ i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ Π j : κ i, M i j) N⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => LinearMap.single R _ (p i)) =
      g.compLinearMap (fun i => LinearMap.single R _ (p i))) : f = g := by
  ext x
  change f (fun i ↦ x i) = g (fun i ↦ x i)
  obtain ⟨i⟩ := nonempty_fintype ι
  have (i : _) := (nonempty_fintype (κ i)).some
  have := Classical.decEq ι
  rw [funext (fun i ↦ Eq.symm (Finset.univ_sum_single (x i)))]
  simp_rw [MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

end Semiring

section piFamily
variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

section Semiring

variable [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, `piFamily f` maps a family of functions (one for each domain `κ i`) into a function
from each selection of indices (with domain `Π i, κ i`).
-/
@[simps]
/-
**MultilinearMap.piFamily** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：piFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p
)) : MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where to
Fun x
参数：f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to se
lect one index from
each family, `piFamily f` maps a family of functions (one for each domain `κ i`)
 into a function
from each selection of indices (with domain `Π i, κ i`).
-/
def piFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where
  toFun x := fun p => f p (fun i => x i (p i))
  map_update_add' {dec} m i x y := funext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, Pi.add_apply, (f p).map_update_add]
  map_update_smul' {dec} m i c x := funext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, Pi.smul_apply, (f p).map_update_smul]

/-- When applied to a family of finitely-supported functions each supported on a single element,
`piFamily` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
/-
**MultilinearMap.piFamily_single** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：piFamily_single [Fintype ι] [forall i, DecidableEq (κ i)] (f : Π (p : Π i,
 κ i), MultilinearMap R (fun i => M i (p i)) (N p)) (p : forall i, κ i) (m : for
all i, M i (p i)) : piFamily f (fun i => Pi.single (p i) (m i)) = Pi.single p (f
 p m)
参数：κ i；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)；p : for
all i, κ i；m : forall i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.piFamily_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} {R : Ty
pe uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [inst : S
emiring R] [inst_1 …
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
When applied to a family of finitely-supported functions each supported on a sin
gle element,
`piFamily` is itself supported on a single element, with value equal to the map 
`f` applied
at that point.
-/
theorem piFamily_single [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    piFamily f (fun i => Pi.single (p i) (m i)) = Pi.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [Pi.single_eq_of_ne' hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [Pi.single_eq_of_ne' hpqi]

/-- When only one member of the family of multilinear maps is nonzero, the result consists only of
the component from that member. -/
@[simp]
/-
**MultilinearMap.piFamily_single_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：piFamily_single_left_apply [Fintype ι] [forall i, DecidableEq (κ i)] (p : 
Π i, κ i) (f : MultilinearMap R (fun i => M i (p i)) (N p)) (x : Π i j, M i j) :
 piFamily (Pi.single p f) x = Pi.single p (f fun i => x i (p i))
参数：κ i；p : Π i, κ i；f : MultilinearMap R (fun i => M i (p i)) (N p)；x : Π i j, M
 i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.piFamily_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} {R : Ty
pe uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [inst : S
emiring R] [inst_1 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…

--- 原说明 ---
When only one member of the family of multilinear maps is nonzero, the result co
nsists only of
the component from that member.
-/
theorem piFamily_single_left_apply [Fintype ι] [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) (x : Π i j, M i j) :
    piFamily (Pi.single p f) x = Pi.single p (f fun i => x i (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]
/-
**MultilinearMap.piFamily_single_left** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`
。
形式化陈述：piFamily_single_left [Fintype ι] [forall i, DecidableEq (κ i)] (p : Π i, κ
 i) (f : MultilinearMap R (fun i => M i (p i)) (N p)) : piFamily (Pi.single p f)
 = (LinearMap.single R _ p).compMultilinearMap (f.compLinearMap fun i => .proj (
p i))
参数：κ i；p : Π i, κ i；f : MultilinearMap R (fun i => M i (p i)) (N p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `MultilinearMap.piFamily_single_left_apply`：piFamily_single_left_apply [F
intype ι] [forall i, DecidableEq (κ i)] (p : Π i, κ i) (f : MultilinearMap R (fu
n i => M i (p i)) (N p)) (x : Π…
-/
theorem piFamily_single_left [Fintype ι] [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (Pi.single p f) =
      (LinearMap.single R _ p).compMultilinearMap (f.compLinearMap fun i => .proj (p i)) :=
  ext <| piFamily_single_left_apply _ _

@[simp]
/-
**MultilinearMap.piFamily_compLinearMap_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Multi
linearMap`。
形式化陈述：piFamily_compLinearMap_lsingle [Fintype ι] [forall i, DecidableEq (κ i)] (
f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)) (p : forall i
, κ i) : (piFamily f).compLinearMap (fun i => LinearMap.single _ _ (p i)) = (Lin
earMap.single _ _ p).compMultilinearMap (f p)
参数：κ i；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)；p : for
all i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `MultilinearMap.piFamily_single`：piFamily_single [Fintype ι] [forall i, D
ecidableEq (κ i)] (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (
N p)) (p : forall i,…
-/
theorem piFamily_compLinearMap_lsingle [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (piFamily f).compLinearMap (fun i => LinearMap.single _ _ (p i))
      = (LinearMap.single _ _ p).compMultilinearMap (f p) :=
  MultilinearMap.ext <| piFamily_single f p

@[simp]
/-
**MultilinearMap.piFamily_zero** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：piFamily_zero : piFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i =>
 M i (p i)) (N p)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.piFamily_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} {R : Ty
pe uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [inst : S
emiring R] [inst_1 …
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piFamily_zero :
    piFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) = 0 := by
  ext; simp

@[simp]
/-
**MultilinearMap.piFamily_add** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：piFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)
) (N p)) : piFamily (f + g) = piFamily f + piFamily g
参数：f g : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.piFamily_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} {R : Ty
pe uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [inst : S
emiring R] [inst_1 …
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MultilinearMap.instIsAddApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (f + g) = piFamily f + piFamily g := by
  ext; simp

@[simp]
/-
**MultilinearMap.piFamily_smul** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：piFamily_smul [Monoid S] [forall p, DistribMulAction S (N p)] [forall p, S
MulCommClass R S (N p)] (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i =
> M i (p i)) (N p)) : piFamily (s • f) = s • piFamily f
参数：N p；N p；s : S；f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N 
p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.piFamily_apply`：∀ {ι : Type uι} {κ : ι → Type uκ} {R : Ty
pe uR} {M : (i : ι) → κ i → Type uM} {N : ((i : ι) → κ i) → Type uN}   [inst : S
emiring R] [inst_1 …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (s • f) = s • piFamily f := by
  ext; simp

end Semiring

section CommSemiring

variable [CommSemiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/-- `MultilinearMap.piFamily` as a linear map. -/
@[simps]
/-
**MultilinearMap.piFamily** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：piFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p
)) : MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where to
Fun x
参数：f : Π (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) (N p)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MultilinearMap.piFamily` as a linear map.
-/
def piFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
      →ₗ[R] MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where
  toFun := piFamily
  map_add' := piFamily_add
  map_smul' := piFamily_smul

end CommSemiring

end piFamily

end MultilinearMap

