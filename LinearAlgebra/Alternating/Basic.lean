/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basis


/-!
# Alternating Maps

We construct the bundled function `AlternatingMap`, which extends `MultilinearMap` with all the
arguments of the same type.

## Main definitions
* `AlternatingMap R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `AddCommMonoid`, `AddCommGroup`, and `Module` structure over `AlternatingMap`s that
  matches the definitions over `MultilinearMap`s.
* `AlternatingMap.domDomCongr`, for permuting the elements within a family.
* `MultilinearMap.alternatization`, which makes an alternating map out of a non-alternating one.
* `AlternatingMap.curryLeft`, for binding the leftmost argument of an alternating map indexed
  by `Fin n.succ`.

## Implementation notes
`AlternatingMap` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `Neg N`.

`AlternatingMap`s are provided with a coercion to `MultilinearMap`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `AlternatingMap.coe_add`
* `AlternatingMap.coe_zero`
* `AlternatingMap.coe_sub`
* `AlternatingMap.coe_neg`
* `AlternatingMap.coe_smul`
-/

@[expose] public section

open Module

-- semiring / add_comm_monoid

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]

-- semiring / add_comm_group

variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {N' : Type*} [AddCommGroup N'] [Module R N']
variable {ι ι' ι'' : Type*}

section

variable (R M N ι)

/-- An alternating map from `ι → M` to `N`, denoted `M [⋀^ι]→ₗ[R] N`,
is a multilinear map that vanishes when two of its arguments are equal. -/
/-
**AlternatingMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   [inst : Semiring R] →     (M : Type u_2) →       [inst_
1 : AddCommMonoid M] →         [_root_.Module R M] →           (N : Type u_3) → 
[inst_3 : AddCommMonoid N] → [_root_.Module R N] → Type u_7 → Type (max (max u_2
 u_3) u_7)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternating map from `ι → M` to `N`, denoted `M [⋀^ι]→ₗ[R] N`,
is a multilinear map that vanishes when two of its arguments are equal.
-/
structure AlternatingMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is alternating: if `v` has two equal coordinates, then `f v = 0`. -/
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → toFun v = 0

@[inherit_doc]
notation M " [⋀^" ι "]→ₗ[" R "] " N:100 => AlternatingMap R M N ι

end

/-- The multilinear map associated to an alternating map -/
add_decl_doc AlternatingMap.toMultilinearMap

namespace AlternatingMap

variable (f f' : M [⋀^ι]→ₗ[R] N)
variable (g g₂ : M [⋀^ι]→ₗ[R] N')
variable (g' : M' [⋀^ι]→ₗ[R] N')
variable (v : ι → M) (v' : ι → M')

open Function

/-! Basic coercion simp lemmas, largely copied from `RingHom` and `MultilinearMap` -/


section Coercions

/-
**AlternatingMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instFunLike : FunLike (M [⋀^ι]->ₗ[R] N) (ι -> M) N where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (M [⋀^ι]→ₗ[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
/-
**AlternatingMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：toFun_eq_coe : f.toFun = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : f.toFun = f :=
  rfl

@[simp]
/-
**AlternatingMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_mk (f : MultilinearMap R (fun _ : ι => M) N) (h) : ⇑(⟨f, h⟩ : M [⋀^ι]-
>ₗ[R] N) = f
参数：f : MultilinearMap R (fun _ : ι => M) N；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : MultilinearMap R (fun _ : ι => M) N) (h) :
    ⇑(⟨f, h⟩ : M [⋀^ι]→ₗ[R] N) = f :=
  rfl
/-
**AlternatingMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_2} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N : Type u_3} [inst_3 : AddCommMonoid N] [i
nst_4 : _root_.Module R N] {ι : Type u_7} {f g : M [⋀^ι]→ₗ[R] N},   f = g → ∀ (x
 : ι → M), f x = g x
参数：x : ι → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem congr_fun {f g : M [⋀^ι]→ₗ[R] N} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : M [⋀^ι]→ₗ[R] N => h x) h
/-
**AlternatingMap.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_2} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {N : Type u_3} [inst_3 : AddCommMonoid N] [i
nst_4 : _root_.Module R N] {ι : Type u_7} (f : M [⋀^ι]→ₗ[R] N)   {x y : ι → M}, 
x = y → f x = f y
参数：f : M [⋀^ι]→ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem congr_arg (f : M [⋀^ι]→ₗ[R] N) {x y : ι → M} (h : x = y) : f x = f y :=
  congr_arg (fun x : ι → M => f x) h
/-
**AlternatingMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_injective : Injective ((↑) : M [⋀^ι]->ₗ[R] N -> (ι -> M) -> N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : Injective ((↑) : M [⋀^ι]→ₗ[R] N → (ι → M) → N) :=
  DFunLike.coe_injective

@[norm_cast]
/-
**AlternatingMap.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_inj {f g : M [⋀^ι]->ₗ[R] N} : (f : (ι -> M) -> N) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AlternatingMap.coe_injective`：coe_injective : Injective ((↑) : M [⋀^ι]->
ₗ[R] N -> (ι -> M) -> N)
-/
theorem coe_inj {f g : M [⋀^ι]→ₗ[R] N} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
/-
**AlternatingMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f' x) : f = f'
参数：H : forall x, f x = f' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f f' : M [⋀^ι]→ₗ[R] N} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

attribute [coe] AlternatingMap.toMultilinearMap
/-
**AlternatingMap.instCoe** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instCoe : Coe (M [⋀^ι]->ₗ[R] N) (MultilinearMap R (fun _ : ι => M) N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoe : Coe (M [⋀^ι]→ₗ[R] N) (MultilinearMap R (fun _ : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]
/-
**AlternatingMap.coe_multilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f :=
  rfl
/-
**AlternatingMap.coe_multilinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Alterna
tingMap`。
形式化陈述：coe_multilinearMap_injective : Function.Injective ((↑) : M [⋀^ι]->ₗ[R] N -
> MultilinearMap R (fun _ : ι => M) N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `MultilinearMap.congr_fun`：congr_fun {f g : MultilinearMap R M₁ M₂} (h : 
f = g) (x : forall i, M₁ i) : f x = g x
-/
theorem coe_multilinearMap_injective :
    Function.Injective ((↑) : M [⋀^ι]→ₗ[R] N → MultilinearMap R (fun _ : ι => M) N) :=
  fun _ _ h => ext <| MultilinearMap.congr_fun h
/-
**AlternatingMap.coe_multilinearMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap
`。
形式化陈述：coe_multilinearMap_mk (f : (ι -> M) -> N) (h₁ h₂ h₃) : ((⟨⟨f, h₁, h₂⟩, h₃⟩
 : M [⋀^ι]->ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) = ⟨f, @h₁, @h₂⟩
参数：f : (ι -> M) -> N；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_multilinearMap_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁, h₂⟩, h₃⟩ : M [⋀^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) =
      ⟨f, @h₁, @h₂⟩ := by
  simp

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.toFun`.
-/


@[simp]
/-
**AlternatingMap.map_update_add** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_add [DecidableEq ι] (i : ι) (x y : M) : f (update v i (x + y)) 
= f (update v i x) + f (update v i y)
参数：i : ι；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_add'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…

--- 原说明 ---
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.toFun`.
-/
theorem map_update_add [DecidableEq ι] (i : ι) (x y : M) :
    f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
  f.map_update_add' v i x y

@[simp]
/-
**AlternatingMap.map_update_sub** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_sub [DecidableEq ι] (i : ι) (x y : M') : g' (update v' i (x - y
)) = g' (update v' i x) - g' (update v' i y)
参数：i : ι；x y : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_sub`：map_update_sub [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f 
(update m i y)
-/
theorem map_update_sub [DecidableEq ι] (i : ι) (x y : M') :
    g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
  g'.toMultilinearMap.map_update_sub v' i x y

@[simp]
/-
**AlternatingMap.map_update_neg** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_neg [DecidableEq ι] (i : ι) (x : M') : g' (update v' i (-x)) = 
-g' (update v' i x)
参数：i : ι；x : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_neg`：map_update_neg [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x : M₁ i) : f (update m i (-x)) = -f (update m i x)
-/
theorem map_update_neg [DecidableEq ι] (i : ι) (x : M') :
    g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.toMultilinearMap.map_update_neg v' i x

@[simp]
/-
**AlternatingMap.map_update_smul** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_smul [DecidableEq ι] (i : ι) (r : R) (x : M) : f (update v i (r
 • x)) = r • f (update v i x)
参数：i : ι；r : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_smul'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι →
 Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid
 (M₁ i)] [inst_2 : Ad…
-/
theorem map_update_smul [DecidableEq ι] (i : ι) (r : R) (x : M) :
    f (update v i (r • x)) = r • f (update v i x) :=
  f.map_update_smul' v i r x

-- Cannot be @[simp] because `i` and `j` cannot be inferred by `simp`.
/-
**AlternatingMap.map_eq_zero_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_eq_zero_of_eq (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j) : 
f v = 0
参数：v : ι -> M；h : v i = v j；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…
-/
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij
/-
**AlternatingMap.map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_coord_zero {m : ι -> M} (i : ι) (h : m i = 0) : f m = 0
参数：i : ι；h : m i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
-/
theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
/-
**AlternatingMap.map_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_zero [DecidableEq ι] (m : ι -> M) (i : ι) : f (update m i 0) = 
0
参数：m : ι -> M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_zero`：map_update_zero [DecidableEq ι] (m : for
all i, M₁ i) (i : ι) : f (update m i 0) = 0
-/
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
/-
**AlternatingMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_zero [Nonempty ι] : f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
-/
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
/-
**AlternatingMap.map_eq_zero_of_not_injective** 是 Mathlib 中的一个定理，位于命名空间 `Alterna
tingMap`。
形式化陈述：map_eq_zero_of_not_injective (v : ι -> M) (hv : ¬Function.Injective v) : f
 v = 0
参数：v : ι -> M；hv : ¬Function.Injective v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), Fu
nction.Injective f = ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
-/
theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 := by
  rw [Function.Injective] at hv
  push Not at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v heq hne

/-!
### Algebraic structure inherited from `MultilinearMap`

`AlternatingMap` carries the same `AddCommMonoid`, `AddCommGroup`, and `Module` structure
as `MultilinearMap`
-/


section SMul

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

/-
**AlternatingMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instSMul : SMul S (M [⋀^ι]->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul S (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
/-
**AlternatingMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：smul_apply (c : S) (m : ι -> M) : (c • f) m = c • f m
参数：c : S；m : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl

@[norm_cast]
/-
**AlternatingMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_smul (c : S) : ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι => M) N
)
参数：c : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (c : S) : ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι => M) N) :=
  rfl
/-
**AlternatingMap.coeFn_smul** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coeFn_smul (c : S) (f : M [⋀^ι]->ₗ[R] N) : ⇑(c • f) = c • ⇑f
参数：c : S；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_smul (c : S) (f : M [⋀^ι]→ₗ[R] N) : ⇑(c • f) = c • ⇑f :=
  rfl
/-
**AlternatingMap.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instSMulCommClass {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommC
lass R T N] [SMulCommClass S T N] : SMulCommClass S T (M [⋀^ι]->ₗ[R] N) where sm
ul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommClass R T N]
    [SMulCommClass S T N] : SMulCommClass S T (M [⋀^ι]→ₗ[R] N) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..
/-
**AlternatingMap.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instIsCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] : IsCe
ntralScalar S (M [⋀^ι]->ₗ[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul N α] [inst_2 : SMul Nᵐᵒᵖ α]   [IsCentralScalar N
 α] [SMulCom…
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

end SMul

/-- The Cartesian product of two alternating maps, as an alternating map. -/
@[simps!]
/-
**AlternatingMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：prod (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P) : M [⋀^ι]->ₗ[R] (N × P)
参数：f : M [⋀^ι]->ₗ[R] N；g : M [⋀^ι]->ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two alternating maps, as an alternating map.
-/
def prod (f : M [⋀^ι]→ₗ[R] N) (g : M [⋀^ι]→ₗ[R] P) : M [⋀^ι]→ₗ[R] (N × P) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }

@[simp]
/-
**AlternatingMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_prod (f : M [⋀^ι]->ₗ[R] N) (g : M [⋀^ι]->ₗ[R] P) : (f.prod g : Multili
nearMap R (fun _ : ι => M) (N × P)) = MultilinearMap.prod f g
参数：f : M [⋀^ι]->ₗ[R] N；g : M [⋀^ι]->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : M [⋀^ι]→ₗ[R] N) (g : M [⋀^ι]→ₗ[R] P) :
    (f.prod g : MultilinearMap R (fun _ : ι => M) (N × P)) = MultilinearMap.prod f g :=
  rfl

/-- Combine a family of alternating maps with the same domain and codomains `N i` into an
alternating map taking values in the space of functions `Π i, N i`. -/
@[simps!]
/-
**AlternatingMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：pi {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [forall 
i, Module R (N i)] (f : forall i, M [⋀^ι]->ₗ[R] N i) : M [⋀^ι]->ₗ[R] (forall i, 
N i)
参数：N i；N i；f : forall i, M [⋀^ι]->ₗ[R] N i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of alternating maps with the same domain and codomains `N i` in
to an
alternating map taking values in the space of functions `Π i, N i`.
-/
def pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [⋀^ι]→ₗ[R] N i) : M [⋀^ι]→ₗ[R] (∀ i, N i) :=
  { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }

@[simp]
/-
**AlternatingMap.coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_pi {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [for
all i, Module R (N i)] (f : forall i, M [⋀^ι]->ₗ[R] N i) : (pi f : MultilinearMa
p R (fun _ : ι => M) (forall i, N i)) = MultilinearMap.pi fun a => f a
参数：N i；N i；f : forall i, M [⋀^ι]->ₗ[R] N i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [⋀^ι]→ₗ[R] N i) :
    (pi f : MultilinearMap R (fun _ : ι => M) (∀ i, N i)) = MultilinearMap.pi fun a => f a :=
  rfl

/-- Given an alternating `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
@[simps!]
/-
**AlternatingMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddComm
Monoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]->ₗ[R] R) (z : M₂) : M₁ [⋀^ι
]->ₗ[R] M₂
参数：f : M₁ [⋀^ι]->ₗ[R] R；z : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an alternating `R`-multilinear map `f` taking values in `R`, `f.smul_right
 z` is the map
sending `m` to `f m • z`.
-/
def smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) : M₁ [⋀^ι]→ₗ[R] M₂ :=
  { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }

@[simp]
/-
**AlternatingMap.coe_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [Add
CommMonoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]->ₗ[R] R) (z : M₂) : (f.
smulRight z : MultilinearMap R (fun _ : ι => M₁) M₂) = MultilinearMap.smulRight 
f z
参数：f : M₁ [⋀^ι]->ₗ[R] R；z : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) :
    (f.smulRight z : MultilinearMap R (fun _ : ι => M₁) M₂) = MultilinearMap.smulRight f z :=
  rfl
/-
**AlternatingMap.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instAdd : Add (M [⋀^ι]->ₗ[R] N) where add a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (M [⋀^ι]→ₗ[R] N) where
  add a b :=
    { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }

@[simp]
/-
**AlternatingMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：add_apply : (f + f') v = f v + f' v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply : (f + f') v = f v + f' v :=
  rfl

@[norm_cast]
/-
**AlternatingMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f' :=
  rfl
/-
**AlternatingMap.instZero** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instZero : Zero (M [⋀^ι]->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (M [⋀^ι]→ₗ[R] N) :=
  ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun _ _ _ _ _ => by simp }⟩

@[simp]
/-
**AlternatingMap.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：zero_apply : (0 : M [⋀^ι]->ₗ[R] N) v = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply : (0 : M [⋀^ι]→ₗ[R] N) v = 0 :=
  rfl

@[norm_cast]
/-
**AlternatingMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_zero : ((0 : M [⋀^ι]->ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) =
 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : M [⋀^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) = 0 :=
  rfl

@[simp]
/-
**AlternatingMap.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：mk_zero : mk (0 : MultilinearMap R (fun _ : ι => M) N) (0 : M [⋀^ι]->ₗ[R] 
N).2 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…
-/
theorem mk_zero :
    mk (0 : MultilinearMap R (fun _ : ι ↦ M) N) (0 : M [⋀^ι]→ₗ[R] N).2 = 0 :=
  rfl
/-
**AlternatingMap.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instInhabited : Inhabited (M [⋀^ι]->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (M [⋀^ι]→ₗ[R] N) :=
  ⟨0⟩
/-
**AlternatingMap.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instAddCommMonoid : AddCommMonoid (M [⋀^ι]->ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (M [⋀^ι]→ₗ[R] N) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _
/-
**AlternatingMap.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instNeg : Neg (M [⋀^ι]->ₗ[R] N')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (M [⋀^ι]→ₗ[R] N') :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
/-
**AlternatingMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：neg_apply (m : ι -> M) : (-g) m = -g m
参数：m : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl

@[norm_cast]
/-
**AlternatingMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_neg : ((-g : M [⋀^ι]->ₗ[R] N') : MultilinearMap R (fun _ : ι => M) N')
 = -g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ((-g : M [⋀^ι]→ₗ[R] N') : MultilinearMap R (fun _ : ι => M) N') = -g :=
  rfl
/-
**AlternatingMap.instSub** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instSub : Sub (M [⋀^ι]->ₗ[R] N')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (M [⋀^ι]→ₗ[R] N') :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]
/-
**AlternatingMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：sub_apply (m : ι -> M) : (g - g₂) m = g m - g₂ m
参数：m : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl

@[norm_cast]
/-
**AlternatingMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂ :=
  rfl
/-
**AlternatingMap.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instAddCommGroup : AddCommGroup (M [⋀^ι]->ₗ[R] N')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (M [⋀^ι]→ₗ[R] N') := fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

section DistribMulAction

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

/-
**AlternatingMap.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`
。
形式化陈述：instDistribMulAction : DistribMulAction S (M [⋀^ι]->ₗ[R] N) where one_smul
 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction : DistribMulAction S (M [⋀^ι]→ₗ[R] N) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

end DistribMulAction

section Module

variable {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
/-
**AlternatingMap.instModule** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instModule : Module S (M [⋀^ι]->ₗ[R] N) where add_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of multilinear maps over an algebra over `R` is a module over `R`, for
 the pointwise
addition and scalar multiplication.
-/
instance instModule : Module S (M [⋀^ι]→ₗ[R] N) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _
/-
**AlternatingMap.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：instIsTorsionFree [IsTorsionFree S N] : IsTorsionFree S (M [⋀^ι]->ₗ[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `AlternatingMap.coe_injective`：coe_injective : Injective ((↑) : M [⋀^ι]->
ₗ[R] N -> (ι -> M) -> N)
· 使用定理 `AlternatingMap.coeFn_smul`：coeFn_smul (c : S) (f : M [⋀^ι]->ₗ[R] N) : ⇑(
c • f) = c • ⇑f
-/
instance instIsTorsionFree [IsTorsionFree S N] : IsTorsionFree S (M [⋀^ι]→ₗ[R] N) :=
  coe_injective.moduleIsTorsionFree _ coeFn_smul

/-- Embedding of alternating maps into multilinear maps as a linear map. -/
@[simps]
/-
**AlternatingMap.toMultilinearMapLM** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：toMultilinearMapLM : (M [⋀^ι]->ₗ[R] N) ->ₗ[S] MultilinearMap R (fun _ : ι 
=> M) N where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of alternating maps into multilinear maps as a linear map.
-/
def toMultilinearMapLM : (M [⋀^ι]→ₗ[R] N) →ₗ[S] MultilinearMap R (fun _ : ι ↦ M) N where
  toFun := toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

section

variable (R M N)

/-- The natural equivalence between linear maps from `M` to `N`
and `1`-multilinear alternating maps from `M` to `N`. -/
@[simps!]
/-
**AlternatingMap.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：ofSubsingleton [Subsingleton ι] (i : ι) : (M ->ₗ[R] N) ≃ (M [⋀^ι]->ₗ[R] N)
 where toFun f
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural equivalence between linear maps from `M` to `N`
and `1`-multilinear alternating maps from `M` to `N`.
-/
def ofSubsingleton [Subsingleton ι] (i : ι) : (M →ₗ[R] N) ≃ (M [⋀^ι]→ₗ[R] N) where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M N i f, fun _ _ _ _ ↦ absurd (Subsingleton.elim _ _)⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
  right_inv _ := coe_multilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

variable (ι) {N}

/-- The constant map is alternating when `ι` is empty. -/
@[simps -fullyApplied]
/-
**AlternatingMap.constOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]->ₗ[R] N
参数：m : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant map is alternating when `ι` is empty.
-/
def constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]→ₗ[R] N :=
  { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
/-
**AlternatingMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：codRestrict (f : M [⋀^ι]->ₗ[R] N) (p : Submodule R N) (h : forall v, f v i
n p) : M [⋀^ι]->ₗ[R] p
参数：f : M [⋀^ι]->ₗ[R] N；p : Submodule R N；h : forall v, f v in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of an alternating map to a submodule.
-/
def codRestrict (f : M [⋀^ι]→ₗ[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    M [⋀^ι]→ₗ[R] p :=
  { f.toMultilinearMap.codRestrict p h with
    toFun := fun v => ⟨f v, h v⟩
    map_eq_zero_of_eq' := fun _ _ _ hv hij => Subtype.ext <| map_eq_zero_of_eq _ _ hv hij }

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable {S : Type*} {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

/-- Composing an alternating map with a linear map on the left gives again an alternating map. -/
/-
**LinearMap.compAlternatingMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compAlternatingMap (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι]->ₗ[R]
 N₂ where __
参数：g : N ->ₗ[R] N₂；f : M [⋀^ι]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing an alternating map with a linear map on the left gives again an altern
ating map.
-/
def compAlternatingMap (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) : M [⋀^ι]→ₗ[R] N₂ where
  __ := g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N)
  map_eq_zero_of_eq' v i j h hij := by simp [f.map_eq_zero_of_eq v h hij]

@[simp]
/-
**LinearMap.coe_compAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_compAlternatingMap (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) : ⇑(g.compA
lternatingMap f) = g ∘ f
参数：g : N ->ₗ[R] N₂；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compAlternatingMap (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) :
    ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl

@[simp]
/-
**LinearMap.compAlternatingMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compAlternatingMap_apply (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) (m : ι ->
 M) : g.compAlternatingMap f m = g (f m)
参数：g : N ->ₗ[R] N₂；f : M [⋀^ι]->ₗ[R] N；m : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compAlternatingMap_apply (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) (m : ι → M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl

@[simp]
/-
**LinearMap.compAlternatingMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compAlternatingMap_zero (g : N ->ₗ[R] N₂) : g.compAlternatingMap (0 : M [⋀
^ι]->ₗ[R] N) = 0
参数：g : N ->ₗ[R] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
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
theorem compAlternatingMap_zero (g : N →ₗ[R] N₂) :
    g.compAlternatingMap (0 : M [⋀^ι]→ₗ[R] N) = 0 :=
  AlternatingMap.ext fun _ => map_zero g

@[simp]
/-
**LinearMap.zero_compAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：zero_compAlternatingMap (f : M [⋀^ι]->ₗ[R] N) : (0 : N ->ₗ[R] N₂).compAlte
rnatingMap f = 0
参数：f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_compAlternatingMap (f : M [⋀^ι]→ₗ[R] N) :
    (0 : N →ₗ[R] N₂).compAlternatingMap f = 0 := rfl

@[simp]
/-
**LinearMap.compAlternatingMap_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compAlternatingMap_add (g : N ->ₗ[R] N₂) (f₁ f₂ : M [⋀^ι]->ₗ[R] N) : g.com
pAlternatingMap (f₁ + f₂) = g.compAlternatingMap f₁ + g.compAlternatingMap f₂
参数：g : N ->ₗ[R] N₂；f₁ f₂ : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem compAlternatingMap_add (g : N →ₗ[R] N₂) (f₁ f₂ : M [⋀^ι]→ₗ[R] N) :
    g.compAlternatingMap (f₁ + f₂) = g.compAlternatingMap f₁ + g.compAlternatingMap f₂ :=
  AlternatingMap.ext fun _ => map_add g _ _

@[simp]
/-
**LinearMap.add_compAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：add_compAlternatingMap (g₁ g₂ : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) : (g₁ +
 g₂).compAlternatingMap f = g₁.compAlternatingMap f + g₂.compAlternatingMap f
参数：g₁ g₂ : N ->ₗ[R] N₂；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_compAlternatingMap (g₁ g₂ : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) :
    (g₁ + g₂).compAlternatingMap f = g₁.compAlternatingMap f + g₂.compAlternatingMap f := rfl

@[simp]
/-
**LinearMap.compAlternatingMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compAlternatingMap_smul [Monoid S] [DistribMulAction S N] [DistribMulActio
n S N₂] [SMulCommClass R S N] [SMulCommClass R S N₂] [CompatibleSMul N N₂ S R] (
g : N ->ₗ[R] N₂) (s : S) (f : M [⋀^ι]->ₗ[R] N) : g.compAlternatingMap (s • f) = 
s • g.compAlternatingMap f
参数：g : N ->ₗ[R] N₂；s : S；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem compAlternatingMap_smul [Monoid S] [DistribMulAction S N] [DistribMulAction S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [CompatibleSMul N N₂ S R]
    (g : N →ₗ[R] N₂) (s : S) (f : M [⋀^ι]→ₗ[R] N) :
    g.compAlternatingMap (s • f) = s • g.compAlternatingMap f :=
  AlternatingMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]
/-
**LinearMap.smul_compAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：smul_compAlternatingMap [Monoid S] [DistribMulAction S N₂] [SMulCommClass 
R S N₂] (g : N ->ₗ[R] N₂) (s : S) (f : M [⋀^ι]->ₗ[R] N) : (s • g).compAlternatin
gMap f = s • g.compAlternatingMap f
参数：g : N ->ₗ[R] N₂；s : S；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_compAlternatingMap [Monoid S] [DistribMulAction S N₂] [SMulCommClass R S N₂]
    (g : N →ₗ[R] N₂) (s : S) (f : M [⋀^ι]→ₗ[R] N) :
    (s • g).compAlternatingMap f = s • g.compAlternatingMap f := rfl

variable (S) in
/-- `LinearMap.compAlternatingMap` as an `S`-linear map. -/
@[simps]
/-
**LinearMap.compAlternatingMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compAlternatingMap (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι]->ₗ[R]
 N₂ where __
参数：g : N ->ₗ[R] N₂；f : M [⋀^ι]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.compAlternatingMap` as an `S`-linear map.
-/
def compAlternatingMapₗ [Semiring S] [Module S N] [Module S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [LinearMap.CompatibleSMul N N₂ S R]
    (g : N →ₗ[R] N₂) :
    (M [⋀^ι]→ₗ[R] N) →ₗ[S] (M [⋀^ι]→ₗ[R] N₂) where
  toFun := g.compAlternatingMap
  map_add' := g.compAlternatingMap_add
  map_smul' := g.compAlternatingMap_smul
/-
**LinearMap._root_.AlternatingMap.smulRight_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlternatingMap.smulRight_eq_comp
    {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) :
    f.smulRight z = (LinearMap.id.smulRight z).compAlternatingMap f :=
  rfl

@[deprecated (since := "2026-05-14")]
alias smulRight_eq_comp := AlternatingMap.smulRight_eq_comp

@[simp]
/-
**LinearMap.subtype_compAlternatingMap_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：subtype_compAlternatingMap_codRestrict (f : M [⋀^ι]->ₗ[R] N) (p : Submodul
e R N) (h) : p.subtype.compAlternatingMap (f.codRestrict p h) = f
参数：f : M [⋀^ι]->ₗ[R] N；p : Submodule R N；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
-/
theorem subtype_compAlternatingMap_codRestrict (f : M [⋀^ι]→ₗ[R] N) (p : Submodule R N)
    (h) : p.subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun _ => rfl

@[simp]
/-
**LinearMap.compAlternatingMap_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：compAlternatingMap_codRestrict (g : N ->ₗ[R] N₂) (f : M [⋀^ι]->ₗ[R] N) (p 
: Submodule R N₂) (h) : (g.codRestrict p h).compAlternatingMap f = (g.compAltern
atingMap f).codRestrict p fun v => h (f v)
参数：g : N ->ₗ[R] N₂；f : M [⋀^ι]->ₗ[R] N；p : Submodule R N₂；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
-/
theorem compAlternatingMap_codRestrict (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N)
    (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compAlternatingMap f =
      (g.compAlternatingMap f).codRestrict p fun v => h (f v) :=
  AlternatingMap.ext fun _ => rfl

end LinearMap

namespace AlternatingMap

variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

/-- Composing an alternating map with the same linear map on each argument gives again an
alternating map. -/
/-
**AlternatingMap.compLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：compLinearMap (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) : M₂ [⋀^ι]->ₗ[R] N
参数：f : M [⋀^ι]->ₗ[R] N；g : M₂ ->ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing an alternating map with the same linear map on each argument gives aga
in an
alternating map.
-/
def compLinearMap (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) : M₂ [⋀^ι]→ₗ[R] N :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }
/-
**AlternatingMap.coe_compLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_compLinearMap (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) : ⇑(f.compLinear
Map g) = f ∘ (g ∘ ·)
参数：f : M [⋀^ι]->ₗ[R] N；g : M₂ ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compLinearMap (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    ⇑(f.compLinearMap g) = f ∘ (g ∘ ·) :=
  rfl

@[simp]
/-
**AlternatingMap.compLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：compLinearMap_apply (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) (v : ι -> M₂) 
: f.compLinearMap g v = f fun i => g (v i)
参数：f : M [⋀^ι]->ₗ[R] N；g : M₂ ->ₗ[R] M；v : ι -> M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compLinearMap_apply (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i => g (v i) :=
  rfl

/-- Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition. -/
/-
**AlternatingMap.compLinearMap_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：compLinearMap_assoc (f : M [⋀^ι]->ₗ[R] N) (g₁ : M₂ ->ₗ[R] M) (g₂ : M₃ ->ₗ[
R] M₂) : (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂)
参数：f : M [⋀^ι]->ₗ[R] N；g₁ : M₂ ->ₗ[R] M；g₂ : M₃ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition.
-/
theorem compLinearMap_assoc (f : M [⋀^ι]→ₗ[R] N) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl

@[simp]
/-
**AlternatingMap.zero_compLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：zero_compLinearMap (g : M₂ ->ₗ[R] M) : (0 : M [⋀^ι]->ₗ[R] N).compLinearMap
 g = 0
参数：g : M₂ ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_compLinearMap (g : M₂ →ₗ[R] M) : (0 : M [⋀^ι]→ₗ[R] N).compLinearMap g = 0 := by
  ext
  simp only [compLinearMap_apply, zero_apply]

@[simp]
/-
**AlternatingMap.add_compLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：add_compLinearMap (f₁ f₂ : M [⋀^ι]->ₗ[R] N) (g : M₂ ->ₗ[R] M) : (f₁ + f₂).
compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g
参数：f₁ f₂ : M [⋀^ι]->ₗ[R] N；g : M₂ ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_compLinearMap (f₁ f₂ : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  simp only [compLinearMap_apply, add_apply]

@[simp]
/-
**AlternatingMap.compLinearMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：compLinearMap_zero [Nonempty ι] (f : M [⋀^ι]->ₗ[R] N) : f.compLinearMap (0
 : M₂ ->ₗ[R] M) = 0
参数：f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compLinearMap_zero [Nonempty ι] (f : M [⋀^ι]→ₗ[R] N) :
    f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp]
/-
**AlternatingMap.compLinearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：compLinearMap_id (f : M [⋀^ι]->ₗ[R] N) : f.compLinearMap LinearMap.id = f
参数：f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'

--- 原说明 ---
Composing an alternating map with the identity linear map in each argument.
-/
theorem compLinearMap_id (f : M [⋀^ι]→ₗ[R] N) : f.compLinearMap LinearMap.id = f :=
  ext fun _ => rfl

/-- Composing with a surjective linear map is injective. -/
/-
**AlternatingMap.compLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingM
ap`。
形式化陈述：compLinearMap_injective (f : M₂ ->ₗ[R] M) (hf : Function.Surjective f) : F
unction.Injective fun g : M [⋀^ι]->ₗ[R] N => g.compLinearMap f
参数：f : M₂ ->ₗ[R] M；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlternatingMap.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {M : Type u
_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Type u_3} [in
st_3 : AddCo…

--- 原说明 ---
Composing with a surjective linear map is injective.
-/
theorem compLinearMap_injective (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : M [⋀^ι]→ₗ[R] N => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [Function.surjInv_eq hf] using AlternatingMap.ext_iff.mp h (Function.surjInv hf ∘ x)
/-
**AlternatingMap.compLinearMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：compLinearMap_inj (f : M₂ ->ₗ[R] M) (hf : Function.Surjective f) (g₁ g₂ : 
M [⋀^ι]->ₗ[R] N) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂
参数：f : M₂ ->ₗ[R] M；hf : Function.Surjective f；g₁ g₂ : M [⋀^ι]->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AlternatingMap.compLinearMap_injective`：compLinearMap_injective (f : M₂ 
->ₗ[R] M) (hf : Function.Surjective f) : Function.Injective fun g : M [⋀^ι]->ₗ[R
] N => g.compLinearMap f
-/
theorem compLinearMap_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : M [⋀^ι]→ₗ[R] N) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- If two `R`-alternating maps from `R` are equal on 1, then they are equal.

This is the alternating version of `LinearMap.ext_ring`. -/
@[ext]
/-
**AlternatingMap.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：ext_ring {R} [CommSemiring R] [Module R N] [Finite ι] ⦃f g : R [⋀^ι]->ₗ[R]
 N⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.coe_multilinearMap_injective`：coe_multilinearMap_injectiv
e : Function.Injective ((↑) : M [⋀^ι]->ₗ[R] N -> MultilinearMap R (fun _ : ι => 
M) N)
· 使用定理 `MultilinearMap.ext_ring`：ext_ring [Finite ι] ⦃f g : MultilinearMap R (fu
n _ : ι => R) M₂⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g

--- 原说明 ---
If two `R`-alternating maps from `R` are equal on 1, then they are equal.

This is the alternating version of `LinearMap.ext_ring`.
-/
theorem ext_ring {R} [CommSemiring R] [Module R N] [Finite ι] ⦃f g : R [⋀^ι]→ₗ[R] N⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g :=
  coe_multilinearMap_injective <| MultilinearMap.ext_ring h

/-- The only `R`-alternating map from two or more copies of `R` is the zero map. -/
/-
**AlternatingMap.uniqueOfCommRing** 是 Mathlib 中的一个实例，位于命名空间 `AlternatingMap`。
形式化陈述：uniqueOfCommRing {R} [CommSemiring R] [Module R N] [Finite ι] [Nontrivial 
ι] : Unique (R [⋀^ι]->ₗ[R] N) where uniq f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The only `R`-alternating map from two or more copies of `R` is the zero map.
-/
instance uniqueOfCommRing {R} [CommSemiring R] [Module R N] [Finite ι] [Nontrivial ι] :
    Unique (R [⋀^ι]→ₗ[R] N) where
  uniq f := let ⟨_, _, hij⟩ := exists_pair_ne ι; ext_ring <| f.map_eq_zero_of_eq _ rfl hij

section DomLcongr

variable (ι R N)
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains.

This is `AlternatingMap.compLinearMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrLeft`.
It could also have been called `LinearEquiv.alternatingMapCongrLeft`. -/
@[simps apply]
/-
**AlternatingMap.domLCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domLCongr (e : M ≃ₗ[R] M₂) : M [⋀^ι]->ₗ[R] N ≃ₗ[S] (M₂ [⋀^ι]->ₗ[R] N) wher
e toFun f
参数：e : M ≃ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a linear equivalence between maps from a linear equivalence between do
mains.

This is `AlternatingMap.compLinearMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrLeft`.
It could also have been called `LinearEquiv.alternatingMapCongrLeft`.
-/
def domLCongr (e : M ≃ₗ[R] M₂) : M [⋀^ι]→ₗ[R] N ≃ₗ[S] (M₂ [⋀^ι]→ₗ[R] N) where
  toFun f := f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := AlternatingMap.ext fun _ => f.congr_arg <| funext fun _ => e.symm_apply_apply _
  right_inv f := AlternatingMap.ext fun _ => f.congr_arg <| funext fun _ => e.apply_symm_apply _

@[simp]
/-
**AlternatingMap.domLCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domLCongr_refl : domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.re
fl S _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
-/
theorem domLCongr_refl : domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ => AlternatingMap.ext fun _ => rfl

@[simp]
/-
**AlternatingMap.domLCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domLCongr_symm (e : M ≃ₗ[R] M₂) : (domLCongr R N ι S e).symm = domLCongr R
 N ι S e.symm
参数：e : M ≃ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domLCongr_symm (e : M ≃ₗ[R] M₂) : (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm :=
  rfl
/-
**AlternatingMap.domLCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domLCongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) : (domLCongr R N ι S e)
.trans (domLCongr R N ι S f) = domLCongr R N ι S (e.trans f)
参数：e : M ≃ₗ[R] M₂；f : M₂ ≃ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domLCongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLCongr R N ι S e).trans (domLCongr R N ι S f) = domLCongr R N ι S (e.trans f) :=
  rfl

end DomLcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp]
/-
**AlternatingMap.compLinearEquiv_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Alternat
ingMap`。
形式化陈述：compLinearEquiv_eq_zero_iff (f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M) : f.com
pLinearMap (g : M₂ ->ₗ[R] M) = 0 ↔ f = 0
参数：f : M [⋀^ι]->ₗ[R] N；g : M₂ ≃ₗ[R] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0

--- 原说明 ---
Composing an alternating map with the same linear equiv on each argument gives t
he zero map
if and only if the alternating map is the zero map.
-/
theorem compLinearEquiv_eq_zero_iff (f : M [⋀^ι]→ₗ[R] N) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLCongr R N ι ℕ g.symm).map_eq_zero_iff

variable (f f' : M [⋀^ι]→ₗ[R] N)
variable (g g₂ : M [⋀^ι]→ₗ[R] N')
variable (g' : M' [⋀^ι]→ₗ[R] N')
variable (v : ι → M) (v' : ι → M')

open Function

/-!
### Other lemmas from `MultilinearMap`
-/


section

/-
**AlternatingMap.map_update_sum** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α -
> M) (m : ι -> M) : f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g 
a))
参数：t : Finset α；i : ι；g : α -> M；m : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_sum`：map_update_sum {α : Type*} [DecidableEq ι
] (t : Finset α) (i : ι) (g : α -> M₁ i) (m : forall i, M₁ i) : f (update m i (∑
 a in t, g a)) = ∑ …
-/
theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M) (m : ι → M) :
    f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) :=
  f.toMultilinearMap.map_update_sum t i g m
/-
**AlternatingMap.map_add_univ** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι -> M) : f (m + m') = ∑ 
s : Finset ι, f (s.piecewise m m')
参数：m m' : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_add_univ`：map_add_univ [DecidableEq ι] [Fintype ι] (m
 m' : forall i, M₁ i) : f (m + m') = ∑ s : Finset ι, f (s.piecewise m m')
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι → M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ m m'
/-
**AlternatingMap.map_smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_smul_univ {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [
Module R M] {N : Type*} [AddCommMonoid N] [Module R N] [Fintype ι] (f : M [⋀^ι]-
>ₗ[R] N) (c : ι -> R) (m : ι -> M) : (f fun i => c i • m i) = (∏ i, c i) • f m
参数：f : M [⋀^ι]->ₗ[R] N；c : ι -> R；m : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
-/
theorem map_smul_univ {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {N : Type*} [AddCommMonoid N] [Module R N] [Fintype ι]
    (f : M [⋀^ι]→ₗ[R] N) (c : ι → R) (m : ι → M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ c m

end

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`AlternatingMap.map_eq_zero_of_eq`.
-/


/-
**AlternatingMap.map_update_self** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_self [DecidableEq ι] {i j : ι} (hij : i != j) : f (Function.upd
ate v i (v j)) = 0
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`AlternatingMap.map_eq_zero_of_eq`.
-/
theorem map_update_self [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (Function.update v i (v j)) = 0 :=
  f.map_eq_zero_of_eq _ (by rw [Function.update_self, Function.update_of_ne hij.symm]) hij
/-
**AlternatingMap.map_update_update** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_update_update [DecidableEq ι] {i j : ι} (hij : i != j) (m : M) : f (Fu
nction.update (Function.update v i m) j m) = 0
参数：hij : i != j；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem map_update_update [DecidableEq ι] {i j : ι} (hij : i ≠ j) (m : M) :
    f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by rw [Function.update_self, Function.update_of_ne hij, Function.update_self]) hij
/-
**AlternatingMap.map_swap_add** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_swap_add [DecidableEq ι] {i j : ι} (hij : i != j) : f (v ∘ Equiv.swap 
i j) + f v = 0
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.comp_swap_eq_update`：comp_swap_eq_update (i j : α) (f : α -> β) : 
f ∘ Equiv.swap i j = update (update f j (f i)) i (f j)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlternatingMap.map_update_add`：map_update_add [DecidableEq ι] (i : ι) (x
 y : M) : f (update v i (x + y)) = f (update v i x) + f (update v i y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_comm`：update_comm {α} [DecidableEq α] {β : α -> Sort*} {
a b : α} (h : a != b) (v : β a) (w : β b) (f : forall a, β a) : update (update f
 a v) b w …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `AlternatingMap.map_update_self`：map_update_self [DecidableEq ι] {i j : ι
} (hij : i != j) : f (Function.update v i (v j)) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlternatingMap.map_update_update`：map_update_update [DecidableEq ι] {i j
 : ι} (hij : i != j) (m : M) : f (Function.update (Function.update v i m) j m) =
 0
-/
theorem map_swap_add [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (v ∘ Equiv.swap i j) + f v = 0 := by
  rw [Equiv.comp_swap_eq_update]
  convert! f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]
/-
**AlternatingMap.map_add_swap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_add_swap [DecidableEq ι] {i j : ι} (hij : i != j) : f v + f (v ∘ Equiv
.swap i j) = 0
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AlternatingMap.map_swap_add`：map_swap_add [DecidableEq ι] {i j : ι} (hij
 : i != j) : f (v ∘ Equiv.swap i j) + f v = 0
-/
theorem map_add_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f v + f (v ∘ Equiv.swap i j) = 0 := by
  rw [add_comm]
  exact f.map_swap_add v hij
/-
**AlternatingMap.map_swap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_swap [DecidableEq ι] {i j : ι} (hij : i != j) : g (v ∘ Equiv.swap i j)
 = -g v
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `AlternatingMap.map_swap_add`：map_swap_add [DecidableEq ι] {i j : ι} (hij
 : i != j) : f (v ∘ Equiv.swap i j) + f v = 0
-/
theorem map_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) : g (v ∘ Equiv.swap i j) = -g v :=
  eq_neg_of_add_eq_zero_left <| g.map_swap_add v hij
/-
**AlternatingMap.map_perm** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_perm [DecidableEq ι] [Fintype ι] (v : ι -> M) (σ : Equiv.Perm ι) : g (
v ∘ σ) = Equiv.Perm.sign σ • g v
参数：v : ι -> M；σ : Equiv.Perm ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_induction_on'`：swap_induction_on' [Finite α] {motive : P
erm α -> Prop} (f : Perm α) (one : motive 1) (mul_swap : forall f x y, x != y ->
 motive f -> motive…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlternatingMap.map_swap`：map_swap [DecidableEq ι] {i j : ι} (hij : i != 
j) : g (v ∘ Equiv.swap i j) = -g v
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
-/
theorem map_perm [DecidableEq ι] [Fintype ι] (v : ι → M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = Equiv.Perm.sign σ • g v := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s x y hxy hI => simp_all [← Function.comp_assoc, g.map_swap]
/-
**AlternatingMap.map_congr_perm** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) : g v = Equi
v.Perm.sign σ • g (v ∘ σ)
参数：σ : Equiv.Perm ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.map_perm`：map_perm [DecidableEq ι] [Fintype ι] (v : ι -> 
M) (σ : Equiv.Perm ι) : g (v ∘ σ) = Equiv.Perm.sign σ • g v
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    g v = Equiv.Perm.sign σ • g (v ∘ σ) := by
  rw [g.map_perm, smul_smul]
  simp

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `MultilinearMap.domDomCongr`. -/
@[simps]
/-
**AlternatingMap.domDomCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι']->ₗ[R] N
参数：σ : ι ≃ ι'；f : M [⋀^ι]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `MultilinearMap.domDomCongr`.
-/
def domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]→ₗ[R] N) : M [⋀^ι']→ₗ[R] N :=
  { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

@[simp]
/-
**AlternatingMap.domDomCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_refl (f : M [⋀^ι]->ₗ[R] N) : f.domDomCongr (Equiv.refl ι) = f
参数：f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem domDomCongr_refl (f : M [⋀^ι]→ₗ[R] N) : f.domDomCongr (Equiv.refl ι) = f := rfl
/-
**AlternatingMap.domDomCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]->ₗ[R] N) : f.
domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂
参数：σ₁ : ι ≃ ι'；σ₂ : ι' ≃ ι''；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

@[simp]
/-
**AlternatingMap.domDomCongr_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_zero (σ : ι ≃ ι') : (0 : M [⋀^ι]->ₗ[R] N).domDomCongr σ = 0
参数：σ : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domDomCongr_zero (σ : ι ≃ ι') : (0 : M [⋀^ι]→ₗ[R] N).domDomCongr σ = 0 :=
  rfl

@[simp]
/-
**AlternatingMap.domDomCongr_add** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_add (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N) : (f + g).domDomCongr
 σ = f.domDomCongr σ + g.domDomCongr σ
参数：σ : ι ≃ ι'；f g : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domDomCongr_add (σ : ι ≃ ι') (f g : M [⋀^ι]→ₗ[R] N) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl

@[simp]
/-
**AlternatingMap.domDomCongr_smul** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommCl
ass R S N] (σ : ι ≃ ι') (c : S) (f : M [⋀^ι]->ₗ[R] N) : (c • f).domDomCongr σ = 
c • f.domDomCongr σ
参数：σ : ι ≃ ι'；c : S；f : M [⋀^ι]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    (σ : ι ≃ ι') (c : S) (f : M [⋀^ι]→ₗ[R] N) :
    (c • f).domDomCongr σ = c • f.domDomCongr σ :=
  rfl

/-- `AlternatingMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
/-
**AlternatingMap.domDomCongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongrEquiv (σ : ι ≃ ι') : M [⋀^ι]->ₗ[R] N ≃+ M [⋀^ι']->ₗ[R] N where 
toFun
参数：σ : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlternatingMap.domDomCongr_add`：domDomCongr_add (σ : ι ≃ ι') (f g : M [⋀
^ι]->ₗ[R] N) : (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ

--- 原说明 ---
`AlternatingMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation.
-/
def domDomCongrEquiv (σ : ι ≃ ι') : M [⋀^ι]→ₗ[R] N ≃+ M [⋀^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    simp [Function.comp_def]
  right_inv m := by
    ext
    simp [Function.comp_def]
  map_add' := domDomCongr_add σ

section DomDomLcongr

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- `AlternatingMap.domDomCongr` as a linear equivalence. -/
@[simps apply symm_apply]
/-
**AlternatingMap.domDomCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι']->ₗ[R] N
参数：σ : ι ≃ ι'；f : M [⋀^ι]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlternatingMap.domDomCongr` as a linear equivalence.
-/
def domDomCongrₗ (σ : ι ≃ ι') : M [⋀^ι]→ₗ[R] N ≃ₗ[S] M [⋀^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp_def]
  right_inv m := by ext; simp [Function.comp_def]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ

@[simp]
/-
**AlternatingMap.domDomCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι']->ₗ[R] N
参数：σ : ι ≃ ι'；f : M [⋀^ι]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domDomCongrₗ_refl :
    (domDomCongrₗ S (Equiv.refl ι) : M [⋀^ι]→ₗ[R] N ≃ₗ[S] M [⋀^ι]→ₗ[R] N) =
      LinearEquiv.refl _ _ :=
  rfl

@[simp]
/-
**AlternatingMap.domDomCongr** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) : M [⋀^ι']->ₗ[R] N
参数：σ : ι ≃ ι'；f : M [⋀^ι]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domDomCongrₗ_toAddEquiv (σ : ι ≃ ι') :
    (↑(domDomCongrₗ S σ : M [⋀^ι]→ₗ[R] N ≃ₗ[S] _) : M [⋀^ι]→ₗ[R] N ≃+ _) =
      domDomCongrEquiv σ :=
  rfl

end DomDomLcongr

/-- The results of applying `domDomCongr` to two maps are equal if and only if those maps are. -/
@[simp]
/-
**AlternatingMap.domDomCongr_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_eq_iff (σ : ι ≃ ι') (f g : M [⋀^ι]->ₗ[R] N) : f.domDomCongr σ 
= g.domDomCongr σ ↔ f = g
参数：σ : ι ≃ ι'；f g : M [⋀^ι]->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.apply_eq_iff_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M]
 [inst_1 : Add N] (e : M ≃+ N) {x y : M}, e x = e y ↔ x = y

--- 原说明 ---
The results of applying `domDomCongr` to two maps are equal if and only if those
 maps are.
-/
theorem domDomCongr_eq_iff (σ : ι ≃ ι') (f g : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ M [⋀^ι']→ₗ[R] N).apply_eq_iff_eq

@[simp]
/-
**AlternatingMap.domDomCongr_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingM
ap`。
形式化陈述：domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : M [⋀^ι]->ₗ[R] N) : f.domDomCongr
 σ = 0 ↔ f = 0
参数：σ : ι ≃ ι'；f : M [⋀^ι]->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZer
oClass M] [inst_1 : AddZeroClass N] (h : M ≃+ N) {x : M}, h x = 0 ↔ x = 0
-/
theorem domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : M [⋀^ι]→ₗ[R] N ≃+ M [⋀^ι']→ₗ[R] N).map_eq_zero_iff
/-
**AlternatingMap.domDomCongr_perm** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：domDomCongr_perm [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : g.domDom
Congr σ = Equiv.Perm.sign σ • g
参数：σ : Equiv.Perm ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `AlternatingMap.map_perm`：map_perm [DecidableEq ι] [Fintype ι] (v : ι -> 
M) (σ : Equiv.Perm ι) : g (v ∘ σ) = Equiv.Perm.sign σ • g v
-/
theorem domDomCongr_perm [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    g.domDomCongr σ = Equiv.Perm.sign σ • g :=
  AlternatingMap.ext fun v => g.map_perm v σ

@[norm_cast]
/-
**AlternatingMap.coe_domDomCongr** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_domDomCongr (σ : ι ≃ ι') : ↑(f.domDomCongr σ) = (f : MultilinearMap R 
(fun _ : ι => M) N).domDomCongr σ
参数：σ : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
-/
theorem coe_domDomCongr (σ : ι ≃ ι') :
    ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι => M) N).domDomCongr σ :=
  MultilinearMap.ext fun _ => rfl

end DomDomCongr

/-- If the arguments are linearly dependent then the result is `0`. -/
/-
**AlternatingMap.map_linearDependent** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_linearDependent {K M N : Type*} [Ring K] [IsDomain K] [AddCommGroup M]
 [Module K M] [AddCommGroup N] [Module K N] [IsTorsionFree K N] (f : M [⋀^ι]->ₗ[
K] N) (v : ι -> M) (h : ¬LinearIndependent K v) : f v = 0
参数：f : M [⋀^ι]->ₗ[K] N；v : ι -> M；h : ¬LinearIndependent K v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_linearIndependent_iff`：not_linearIndependent_iff : ¬LinearIndependen
t R v ↔ exists s : Finset ι, exists g : ι -> R, ∑ i in s, g i • v i = 0 ∧ exists
 i in s, g i !=…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `AlternatingMap.map_update_neg`：map_update_neg [DecidableEq ι] (i : ι) (x
 : M') : g' (update v' i (-x)) = -g' (update v' i x)
· 使用定理 `AlternatingMap.map_update_sum`：map_update_sum {α : Type*} [DecidableEq ι
] (t : Finset α) (i : ι) (g : α -> M) (m : ι -> M) : f (update m i (∑ a in t, g 
a)) = ∑ a in t, f (…
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `AlternatingMap.map_update_smul`：map_update_smul [DecidableEq ι] (i : ι) 
(r : R) (x : M) : f (update v i (r • x)) = r • f (update v i x)
· 使用定理 `AlternatingMap.map_update_self`：map_update_self [DecidableEq ι] {i j : ι
} (hij : i != j) : f (Function.update v i (v j)) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f

--- 原说明 ---
If the arguments are linearly dependent then the result is `0`.
-/
theorem map_linearDependent {K M N : Type*} [Ring K] [IsDomain K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [IsTorsionFree K N] (f : M [⋀^ι]→ₗ[K] N)
    (v : ι → M) (h : ¬LinearIndependent K v) : f v = 0 := by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  let := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_update_smul, Function.update_eq_self, smul_eq_zero] at this
    exact Or.resolve_left this hz
  rw [← Finset.insert_erase hi, Finset.sum_insert (s.notMem_erase i), add_eq_zero_iff_eq_neg] at h
  rw [h, f.map_update_neg, f.map_update_sum, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hij, _⟩ := Finset.mem_erase.mp hj
  rw [f.map_update_smul, f.map_update_self _ hij.symm, smul_zero]

section Fin

open Fin

/-- A version of `MultilinearMap.cons_add` for `AlternatingMap`. -/
/-
**AlternatingMap.map_vecCons_add** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_vecCons_add {n : Nat} (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : Fin n -> M) 
(x y : M) : f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.ve
cCons y m)
参数：f : M [⋀^Fin n.succ]->ₗ[R] N；m : Fin n -> M；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.cons_add`：cons_add (f : MultilinearMap R M M₂) (m : foral
l i : Fin n, M i.succ) (x y : M 0) : f (cons (x + y) m) = f (cons x m) + f (cons
 y m)

--- 原说明 ---
A version of `MultilinearMap.cons_add` for `AlternatingMap`.
-/
theorem map_vecCons_add {n : ℕ} (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _

/-- A version of `MultilinearMap.cons_smul` for `AlternatingMap`. -/
/-
**AlternatingMap.map_vecCons_smul** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：map_vecCons_smul {n : Nat} (f : M [⋀^Fin n.succ]->ₗ[R] N) (m : Fin n -> M)
 (c : R) (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m)
参数：f : M [⋀^Fin n.succ]->ₗ[R] N；m : Fin n -> M；c : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.cons_smul`：cons_smul (f : MultilinearMap R M M₂) (m : for
all i : Fin n, M i.succ) (c : R) (x : M 0) : f (cons (c • x) m) = c • f (cons x 
m)

--- 原说明 ---
A version of `MultilinearMap.cons_smul` for `AlternatingMap`.
-/
theorem map_vecCons_smul {n : ℕ} (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (c : R)
    (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _

end Fin

end AlternatingMap

namespace MultilinearMap

open Equiv

variable [Fintype ι] [DecidableEq ι]

/-
**MultilinearMap.alternization_map_eq_zero_of_eq_aux** 是 Mathlib 中的一个定理，位于命名空间 `
MultilinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun _ : ι => M) N')
    (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
    (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ) v = 0 := by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ

/-- Produce an `AlternatingMap` out of a `MultilinearMap`, by summing over all argument
permutations. -/
/-
**MultilinearMap.alternatization** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：alternatization : MultilinearMap R (fun _ : ι => M) N' ->+ M [⋀^ι]->ₗ[R] N
' where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce an `AlternatingMap` out of a `MultilinearMap`, by summing over all argum
ent
permutations.
-/
def alternatization : MultilinearMap R (fun _ : ι => M) N' →+ M [⋀^ι]→ₗ[R] N' where
  toFun m :=
    { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := private fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by ext; simp [Finset.sum_add_distrib]
  map_zero' := by ext; simp
/-
**MultilinearMap.alternatization_def** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：alternatization_def (m : MultilinearMap R (fun _ : ι => M) N') : ⇑(alterna
tization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :)
参数：m : MultilinearMap R (fun _ : ι => M) N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatization_def (m : MultilinearMap R (fun _ : ι => M) N') :
    ⇑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :) :=
  rfl
/-
**MultilinearMap.alternatization_coe** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：alternatization_coe (m : MultilinearMap R (fun _ : ι => M) N') : ↑(alterna
tization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :)
参数：m : MultilinearMap R (fun _ : ι => M) N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.coe_injective`：coe_injective : Injective ((↑) : Multiline
arMap R M₁ M₂ -> (forall i, M₁ i) -> M₂)
-/
theorem alternatization_coe (m : MultilinearMap R (fun _ : ι => M) N') :
    ↑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :) :=
  coe_injective rfl
/-
**MultilinearMap.alternatization_apply** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap
`。
形式化陈述：alternatization_apply (m : MultilinearMap R (fun _ : ι => M) N') (v : ι ->
 M) : alternatization m v = ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ v
参数：m : MultilinearMap R (fun _ : ι => M) N'；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.instIsAddApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatization_apply (m : MultilinearMap R (fun _ : ι => M) N') (v : ι → M) :
    alternatization m v = ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ v := by
  simp only [alternatization_def, smul_apply, sum_apply]

end MultilinearMap

namespace AlternatingMap

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
/-
**AlternatingMap.coe_alternatization** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：coe_alternatization [DecidableEq ι] [Fintype ι] (a : M [⋀^ι]->ₗ[R] N') : M
ultilinearMap.alternatization (a : MultilinearMap R (fun _ => M) N') = Nat.facto
rial (Fintype.card ι) • a
参数：a : M [⋀^ι]->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.coe_injective`：coe_injective : Injective ((↑) : M [⋀^ι]->
ₗ[R] N -> (ι -> M) -> N)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AlternatingMap.domDomCongr_perm`：domDomCongr_perm [Fintype ι] [Decidable
Eq ι] (σ : Equiv.Perm ι) : g.domDomCongr σ = Equiv.Perm.sign σ • g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_perm`：Fintype.card_perm [Fintype α] : Fintype.card (Perm α)
 = (Fintype.card α)!
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Alternatizing a multilinear map that is already alternating results in a scale f
actor of `n!`,
where `n` is the number of inputs.
-/
theorem coe_alternatization [DecidableEq ι] [Fintype ι] (a : M [⋀^ι]→ₗ[R] N') :
    MultilinearMap.alternatization (a : MultilinearMap R (fun _ => M) N')
    = Nat.factorial (Fintype.card ι) • a := by
  apply AlternatingMap.coe_injective
  simp_rw [MultilinearMap.alternatization_def, ← coe_domDomCongr, domDomCongr_perm, coe_smul,
    smul_smul, Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinearMap, coe_smul]

end AlternatingMap

namespace LinearMap

variable {N'₂ : Type*} [AddCommGroup N'₂] [Module R N'₂] [DecidableEq ι] [Fintype ι]

/-- Composition with a linear map before and after alternatization are equivalent. -/
/-
**LinearMap.compMultilinearMap_alternatization** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：compMultilinearMap_alternatization (g : N' ->ₗ[R] N'₂) (f : MultilinearMap
 R (fun _ : ι => M) N') : MultilinearMap.alternatization (g.compMultilinearMap f
) = g.compAlternatingMap (MultilinearMap.alternatization f)
参数：g : N' ->ₗ[R] N'₂；f : MultilinearMap R (fun _ : ι => M) N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.compMultilinearMap_domDomCongr`：compMultilinearMap_domDomCongr
 (σ : ι₁ ≃ ι₂) (g : M₂ ->ₗ[R] M₃) (f : MultilinearMap R (fun _ : ι₁ => M') M₂) :
 (g.compMultilinearMap f).domD…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `MultilinearMap.instIsZeroApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ 
: ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommM
onoid (M₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.instIsAddApplyForall`：∀ {R : Type uR} {ι : Type uι} {M₁ :
 ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMo
noid (M₁ i)] [inst_2 : Ad…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MultilinearMap.instIsSMulApplyForall`：∀ {R : Type uR} {S : Type uS} {ι :
 Type uι} {M₁ : ι → Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i :
 ι) → AddCommMonoid (M₁ i)…
· 使用定理 `MultilinearMap.domDomCongr_apply`：∀ {R : Type uR} {M₂ : Type v₂} {M₃ : T
ype v₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   [inst_2 : AddCommMonoi
d M₃] [inst_3 : _root_…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_zsmul_unit`：∀ {F : Type u_16} {M : Type u_17} {N : Type u_18} [inst 
: AddGroup M] [inst_1 : AddGroup N] [inst_2 : FunLike F M N]   [AddMonoidHomClas
s F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Composition with a linear map before and after alternatization are equivalent.
-/
theorem compMultilinearMap_alternatization (g : N' →ₗ[R] N'₂)
    (f : MultilinearMap R (fun _ : ι => M) N') :
    MultilinearMap.alternatization (g.compMultilinearMap f)
      = g.compAlternatingMap (MultilinearMap.alternatization f) := by
  ext
  simp [MultilinearMap.alternatization_def]

end LinearMap

section Basis

open AlternatingMap

variable {ι₁ : Type*} [Finite ι]
variable {R' : Type*} {N₁ N₂ : Type*} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Module R' N₁] [Module R' N₂]

/-- Two alternating maps indexed by a `Fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
/-
**Module.Basis.ext_alternating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.ext_alternating {f g : N₁ [⋀^ι]->ₗ[R'] N₂} (e : Basis ι₁ R' N
₁) (h : forall v : ι -> ι₁, Function.Injective v -> (f fun i => e (v i)) = g fun
 i => e (v i)) : f = g
参数：e : Basis ι₁ R' N₁；h : forall v : ι -> ι₁, Function.Injective v -> (f fun i =
> e (v i)) = g fun i => e (v i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.coe_multilinearMap_injective`：coe_multilinearMap_injectiv
e : Function.Injective ((↑) : M [⋀^ι]->ₗ[R] N -> MultilinearMap R (fun _ : ι => 
M) N)
· 使用定理 `Module.Basis.ext_multilinear`：Module.Basis.ext_multilinear [Finite ι] {f
 g : MultilinearMap R M N} {ιM : ι -> Type*} (e : forall i, Basis (ιM i) R (M i)
) (h : forall v : …
· 使用定理 `Not.imp`：∀ {a b : Prop}, ¬b → (a → b) → ¬a
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlternatingMap.coe_multilinearMap`：coe_multilinearMap : ⇑(f : Multilinea
rMap R (fun _ : ι => M) N) = f
· 使用定理 `AlternatingMap.map_eq_zero_of_not_injective`：map_eq_zero_of_not_injectiv
e (v : ι -> M) (hv : ¬Function.Injective v) : f v = 0

--- 原说明 ---
Two alternating maps indexed by a `Fintype` are equal if they are equal when all
 arguments
are distinct basis vectors.
-/
theorem Module.Basis.ext_alternating {f g : N₁ [⋀^ι]→ₗ[R'] N₂} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i => e (v i)) = g fun i => e (v i)) :
    f = g := by
  refine AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ ↦ e) fun v => ?_)
  by_cases hi : Function.Injective v
  · exact h v hi
  · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
    rw [coe_multilinearMap, coe_multilinearMap, f.map_eq_zero_of_not_injective _ this,
      g.map_eq_zero_of_not_injective _ this]

end Basis

variable {R' : Type*} {M'' M₂'' N'' N₂'' : Type*} [CommSemiring R'] [AddCommMonoid M'']
  [AddCommMonoid M₂''] [AddCommMonoid N''] [AddCommMonoid N₂''] [Module R' M''] [Module R' M₂'']
  [Module R' N''] [Module R' N₂'']

/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `Linear.compAlternatingMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrRight`. -/
@[simps!]
/-
**LinearEquiv.alternatingMapCongrRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.alternatingMapCongrRight (e : N'' ≃ₗ[R'] N₂'') : M'' [⋀^ι]->ₗ[
R'] N'' ≃ₗ[R'] (M'' [⋀^ι]->ₗ[R'] N₂'') where toFun f
参数：e : N'' ≃ₗ[R'] N₂''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `Linear.compAlternatingMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrRight`.
-/
def LinearEquiv.alternatingMapCongrRight (e : N'' ≃ₗ[R'] N₂'') :
    M'' [⋀^ι]→ₗ[R'] N'' ≃ₗ[R'] (M'' [⋀^ι]→ₗ[R'] N₂'') where
  toFun f := e.compAlternatingMap f
  invFun f := e.symm.compAlternatingMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
/-
**AlternatingMap.constLinearEquivOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlternatingMap.constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] (M'' [⋀^
ι]->ₗ[R'] N'') where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of constant maps is equivalent to the space of maps that are alternati
ng with respect
to an empty family.
-/
def AlternatingMap.constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] (M'' [⋀^ι]→ₗ[R'] N'') where
  toFun := AlternatingMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  right_inv f := ext fun _ => AlternatingMap.congr_arg f <| Subsingleton.elim _ _
