/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basics on bilinear maps

This file provides basics on bilinear maps. The most general form considered are maps that are
semilinear in both arguments. They are of type `M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P`, where `M` and `N`
are modules over `R` and `S` respectively, `P` is a module over both `R₂` and `S₂` with
commuting actions, and `ρ₁₂ : R →+* R₂` and `σ₁₂ : S →+* S₂`.

## Main declarations

* `LinearMap.mk₂`: a constructor for bilinear maps,
  taking an unbundled function together with proof witnesses of bilinearity
* `LinearMap.flip`: turns a bilinear map `M × N → P` into `N × M → P`
* `LinearMap.lflip`: given a linear map from `M` to `N →ₗ[R] P`, i.e., a bilinear map `M → N → P`,
  change the order of variables and get a linear map from `N` to `M →ₗ[R] P`.
* `LinearMap.lcomp`: composition of a given linear map `M → N` with a linear map `N → P` as
  a linear map from `Nₗ →ₗ[R] Pₗ` to `M →ₗ[R] Pₗ`
* `LinearMap.llcomp`: composition of linear maps as a bilinear map from `(M →ₗ[R] N) × (N →ₗ[R] P)`
  to `M →ₗ[R] P`
* `LinearMap.compl₂`: composition of a linear map `Q → N` and a bilinear map `M → N → P` to
  form a bilinear map `M → Q → P`.
* `LinearMap.compr₂`: composition of a linear map `P → Q` and a bilinear map `M → N → P` to form a
  bilinear map `M → N → Q`.
* `LinearMap.lsmul`: scalar multiplication as a bilinear map `R × M → M`

## Tags

bilinear
-/

@[expose] public section

open Function Module

namespace LinearMap

section Semiring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {R R₂ S S₂ : Type*} [Semiring R] [Semiring R₂] [Semiring S] [Semiring S₂]
variable {M M₂ N N₂ P P₂ Pₗ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid N]
variable [AddCommMonoid N₂] [AddCommMonoid P] [AddCommMonoid P₂] [AddCommMonoid Pₗ]
variable [Module R M] [Module R M₂] [Module S N] [Module S N₂] [Module R₂ P] [Module S₂ P]
variable [Module R P₂] [Module S₂ P₂] [Module R Pₗ] [Module S Pₗ]
variable {M' P' : Type*} [AddCommGroup M'] [AddCommGroup P']
variable [Module R M'] [Module R₂ P'] [Module S₂ P']
variable [SMulCommClass S₂ R₂ P] [SMulCommClass S R Pₗ] [SMulCommClass S₂ R₂ P']
variable [SMulCommClass S₂ R P₂]
variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}
variable (ρ₁₂ σ₁₂)

-- TODO: refactor to use a structure holding the assumptions, as in `IsBilinearMap` below.
/-- Create a bilinear map from a function that is semilinear in each component.
See `mk₂'` and `mk₂` for the linear case. -/
/-
**LinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_16} →         
    {M₂ : Type u_17} →               [inst_2 : AddCommMonoid M] →               
  [inst_3 : AddCommMonoid M₂] →                   [inst_4 : _root_.Module R M] →
                     [inst_5 : _root_.Module S M₂] →                       (toAd
dHom : M →ₙ+ M₂) →                         (∀ (m : R) (x : M), toAddHom.toFun (m
 • x) = σ m • toAddHom.toFun x) → M →ₛₗ[σ] M₂
参数：toAddHom : M →ₙ+ M₂；∀ (m : R) (x : M), toAddHom.toFun (m • x) = σ m • toAddHo
m.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a bilinear map from a function that is semilinear in each component.
See `mk₂'` and `mk₂` for the linear case.
-/
def mk₂'ₛₗ (f : M → N → P) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = ρ₁₂ c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = σ₁₂ c • f m n) : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P where
  toFun m :=
    { toFun := f m
      map_add' := H3 m
      map_smul' := fun c => H4 c m }
  map_add' m₁ m₂ := LinearMap.ext <| H1 m₁ m₂
  map_smul' c m := LinearMap.ext <| H2 c m

variable {ρ₁₂ σ₁₂}

@[simp]
/-
**LinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_16} →         
    {M₂ : Type u_17} →               [inst_2 : AddCommMonoid M] →               
  [inst_3 : AddCommMonoid M₂] →                   [inst_4 : _root_.Module R M] →
                     [inst_5 : _root_.Module S M₂] →                       (toAd
dHom : M →ₙ+ M₂) →                         (∀ (m : R) (x : M), toAddHom.toFun (m
 • x) = σ m • toAddHom.toFun x) → M →ₛₗ[σ] M₂
参数：toAddHom : M →ₙ+ M₂；∀ (m : R) (x : M), toAddHom.toFun (m • x) = σ m • toAddHo
m.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk₂'ₛₗ_apply (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
    (mk₂'ₛₗ ρ₁₂ σ₁₂ f H1 H2 H3 H4 : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) m n = f m n := rfl

variable (R S)

/-- Create a bilinear map from a function that is linear in each component.
See `mk₂` for the special case where both arguments come from modules over the same ring. -/
/-
**LinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_16} →         
    {M₂ : Type u_17} →               [inst_2 : AddCommMonoid M] →               
  [inst_3 : AddCommMonoid M₂] →                   [inst_4 : _root_.Module R M] →
                     [inst_5 : _root_.Module S M₂] →                       (toAd
dHom : M →ₙ+ M₂) →                         (∀ (m : R) (x : M), toAddHom.toFun (m
 • x) = σ m • toAddHom.toFun x) → M →ₛₗ[σ] M₂
参数：toAddHom : M →ₙ+ M₂；∀ (m : R) (x : M), toAddHom.toFun (m • x) = σ m • toAddHo
m.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a bilinear map from a function that is linear in each component.
See `mk₂` for the special case where both arguments come from modules over the s
ame ring.
-/
def mk₂' (f : M → N → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = c • f m n) : M →ₗ[R] N →ₗ[S] Pₗ :=
  mk₂'ₛₗ (RingHom.id R) (RingHom.id S) f H1 H2 H3 H4

variable {R S}

@[simp]
/-
**LinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_16} →         
    {M₂ : Type u_17} →               [inst_2 : AddCommMonoid M] →               
  [inst_3 : AddCommMonoid M₂] →                   [inst_4 : _root_.Module R M] →
                     [inst_5 : _root_.Module S M₂] →                       (toAd
dHom : M →ₙ+ M₂) →                         (∀ (m : R) (x : M), toAddHom.toFun (m
 • x) = σ m • toAddHom.toFun x) → M →ₛₗ[σ] M₂
参数：toAddHom : M →ₙ+ M₂；∀ (m : R) (x : M), toAddHom.toFun (m • x) = σ m • toAddHo
m.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk₂'_apply (f : M → N → Pₗ) {H1 H2 H3 H4} (m : M) (n : N) :
    (mk₂' R S f H1 H2 H3 H4 : M →ₗ[R] N →ₗ[S] Pₗ) m n = f m n := rfl
/-
**LinearMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (H : ∀ m n, f m n = g m n) : f = g :=
  LinearMap.ext fun m => LinearMap.ext fun n => H m n
/-
**LinearMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} {f g : M →ₛₗ[σ] M₃}, f = g → ∀ (x : M), f x = g x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem congr_fun₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : f = g) (x y) : f x y = g x y :=
  LinearMap.congr_fun (LinearMap.congr_fun h x) y
/-
**LinearMap.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} {f g : M →ₛₗ[σ] M₃}, f = g ↔ ∀ (x : M), f x = g x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem ext_iff₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} : f = g ↔ ∀ m n, f m n = g m n :=
  ⟨congr_fun₂, ext₂⟩

section

attribute [local instance] SMulCommClass.symm

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
/-
**LinearMap.flip** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : N ->ₛₗ[σ₁₂] M ->ₛₗ[ρ₁₂] P
参数：f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map
 from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps 
from `M` to `P`.
-/
def flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P :=
  mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun _ _ m => (f m).map_add _ _)
    (fun _ _ m => (f m).map_smulₛₗ _ _)
    (fun n m₁ m₂ => by simp only [map_add, add_apply])
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`.
    -- It looks like we now run out of assignable metavariables.
    (fun c n m => by simp only [map_smulₛₗ _, smul_apply])

@[simp]
/-
**LinearMap.flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：flip_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = 
f m n
参数：f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
theorem flip_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = f m n := rfl

end

section Semiring

variable {R R₂ R₃ R₄ R₅ : Type*}
variable {M N P Q : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄] [Semiring R₅]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} {σ₄₂ : R₄ →+* R₂} {σ₄₃ : R₄ →+* R₃}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R₂ N] [Module R₃ P] [Module R₄ Q] [Module R₅ P]
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₄₂ σ₂₃ σ₄₃]
variable [SMulCommClass R₃ R₅ P] {σ₁₅ : R →+* R₅}

variable (R₅ P σ₂₃)

/-- Composing a semilinear map `M → N` and a semilinear map `N → P` to form a semilinear map
`M → P` is itself a linear map. -/
/-
**LinearMap.lcomp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lcomp (f : M ->ₗ[R] M₂) : (M₂ ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] N
参数：f : M ->ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a semilinear map `M → N` and a semilinear map `N → P` to form a semili
near map
`M → P` is itself a linear map.
-/
def lcompₛₗ (f : M →ₛₗ[σ₁₂] N) : (N →ₛₗ[σ₂₃] P) →ₗ[R₅] M →ₛₗ[σ₁₃] P :=
  letI := SMulCommClass.symm
  flip <| LinearMap.comp (flip id) f

variable {P σ₂₃ R₅}

@[simp]
/-
**LinearMap.lcomp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lcomp (f : M ->ₗ[R] M₂) : (M₂ ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] N
参数：f : M ->ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcompₛₗ_apply (f : M →ₛₗ[σ₁₂] N) (g : N →ₛₗ[σ₂₃] P) (x : M) :
    lcompₛₗ R₅ P σ₂₃ f g x = g (f x) := rfl


/-- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`. -/
/-
**LinearMap.compl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`.
-/
def compl₂ (h : M →ₛₗ[σ₁₅] N →ₛₗ[σ₂₃] P) (g : Q →ₛₗ[σ₄₂] N) : M →ₛₗ[σ₁₅] Q →ₛₗ[σ₄₃] P where
  toFun a := (lcompₛₗ R₅ P σ₂₃ g) (h a)
  map_add' _ _ := by
    simp [map_add]
  map_smul' _ _ := by
    simp [map_smulₛₗ, lcompₛₗ]

@[simp]
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₂_apply (h : M →ₛₗ[σ₁₅] N →ₛₗ[σ₂₃] P) (g : Q →ₛₗ[σ₄₂] N) (m : M) (q : Q) :
    h.compl₂ g m q = h m (g q) := rfl

@[simp]
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₂_id (h : M →ₛₗ[σ₁₅] N →ₛₗ[σ₂₃] P) : h.compl₂ LinearMap.id = h := by
  ext
  rw [compl₂_apply, id_coe, _root_.id]
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₂_comp {R₆ Q' : Type*} [Semiring R₆] [AddCommMonoid Q'] [Module R₆ Q']
    {σ₆₂ : R₆ →+* R₂} {σ₆₃ : R₆ →+* R₃} {σ₆₄ : R₆ →+* R₄}
    [RingHomCompTriple σ₆₂ σ₂₃ σ₆₃] [RingHomCompTriple σ₆₄ σ₄₂ σ₆₂] [RingHomCompTriple σ₆₄ σ₄₃ σ₆₃]
    (h : M →ₛₗ[σ₁₅] N →ₛₗ[σ₂₃] P) (g : Q →ₛₗ[σ₄₂] N) (f : Q' →ₛₗ[σ₆₄] Q) :
    h.compl₂ (g ∘ₛₗ f) = (h.compl₂ g).compl₂ f := rfl

end Semiring

section lcomp

variable (S N) [Module R N] [SMulCommClass R S N]

/-- Composing a given linear map `M → N` with a linear map `N → P` as a linear map from
`Nₗ →ₗ[R] Pₗ` to `M →ₗ[R] Pₗ`. -/
/-
**LinearMap.lcomp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lcomp (f : M ->ₗ[R] M₂) : (M₂ ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] N
参数：f : M ->ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a given linear map `M → N` with a linear map `N → P` as a linear map f
rom
`Nₗ →ₗ[R] Pₗ` to `M →ₗ[R] Pₗ`.
-/
def lcomp (f : M →ₗ[R] M₂) : (M₂ →ₗ[R] N) →ₗ[S] M →ₗ[R] N :=
  lcompₛₗ _ _ _ f

variable {S N}

@[simp]
/-
**LinearMap.lcomp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lcomp_apply (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N) (x : M) : lcomp S N f g x 
= g (f x)
参数：f : M ->ₗ[R] M₂；g : M₂ ->ₗ[R] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcomp_apply (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] N) (x : M) : lcomp S N f g x = g (f x) := rfl
/-
**LinearMap.lcomp_apply'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lcomp_apply' (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N) : lcomp S N f g = g ∘ₗ f
参数：f : M ->ₗ[R] M₂；g : M₂ ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcomp_apply' (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] N) : lcomp S N f g = g ∘ₗ f := rfl
/-
**LinearMap.lcomp_injective_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：lcomp_injective_of_surjective (g : M ->ₗ[R] M₂) (surj : Function.Surjectiv
e g) : Function.Injective (LinearMap.lcomp S N g)
参数：g : M ->ₗ[R] M₂；surj : Function.Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.injective_linearMapComp_right`：∀ {R₁ : Type u_2} {R₂
 : Type u_3} {R₃ : Type u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [
inst : Semiring R₁]   [inst_1 : Semirin…
-/
lemma lcomp_injective_of_surjective (g : M →ₗ[R] M₂) (surj : Function.Surjective g) :
    Function.Injective (LinearMap.lcomp S N g) :=
  surj.injective_linearMapComp_right

end lcomp

attribute [local instance] SMulCommClass.symm

@[simp]
/-
**LinearMap.flip_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：flip_flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : f.flip.flip = f
参数：f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.flip_apply`：flip_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M)
 (n : N) : flip f n m = f m n
-/
theorem flip_flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : f.flip.flip = f :=
  LinearMap.ext₂ fun _x _y => (f.flip.flip_apply _ _).trans (f.flip_apply _ _)
/-
**LinearMap.flip_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：flip_inj {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : flip f = flip g) : f = g
参数：H : flip f = flip g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem flip_inj {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (H : flip f = flip g) : f = g :=
  ext₂ fun m n => show flip f n m = flip g n m by rw [H]
/-
**LinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃), f 0 = 0
参数：f : M →ₛₗ[σ] M₃。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem map_zero₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (y) : f 0 y = 0 :=
  (flip f y).map_zero
/-
**LinearMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : Type u_10} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGro
up M₂] {module_M : _root_.Module R M} {module_M₂ : _root_.Module S M₂}   {σ : R 
→+* S} (f : M →ₛₗ[σ] M₂) (x : M), f (-x) = -f x
参数：f : M →ₛₗ[σ] M₂；x : M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem map_neg₂ (f : M' →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P') (x y) : f (-x) y = -f x y :=
  (flip f y).map_neg _
/-
**LinearMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : Type u_10} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGro
up M₂] {module_M : _root_.Module R M} {module_M₂ : _root_.Module S M₂}   {σ : R 
→+* S} (f : M →ₛₗ[σ] M₂) (x y : M), f (x - y) = f x - f y
参数：f : M →ₛₗ[σ] M₂；x y : M；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem map_sub₂ (f : M' →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P') (x y z) : f (x - y) z = f x z - f y z :=
  (flip f z).map_sub _ _
/-
**LinearMap.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃) (x y : M), f (x + y) = f x + f y
参数：f : M →ₛₗ[σ] M₃；x y : M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem map_add₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y :=
  (flip f y).map_add _ _
/-
**LinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst
_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R M₂] (fₗ : M →ₗ[R] M₂) (c : R)   (x : M), fₗ (c • x) =
 c • fₗ x
参数：fₗ : M →ₗ[R] M₂；c : R；x : M；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem map_smul₂ (f : M₂ →ₗ[R] N₂ →ₛₗ[σ₁₂] P₂) (r : R) (x y) : f (r • x) y = r • f x y :=
  (flip f y).map_smul _ _
/-
**LinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst
_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R M₂] (fₗ : M →ₗ[R] M₂) (c : R)   (x : M), fₗ (c • x) =
 c • fₗ x
参数：fₗ : M →ₗ[R] M₂；c : R；x : M；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem map_smulₛₗ₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (r : R) (x y) : f (r • x) y = ρ₁₂ r • f x y :=
  (flip f y).map_smulₛₗ _ _
/-
**LinearMap.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_sum₂ {ι : Type*} (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (t : Finset ι) (x : ι → M) (y) :
    f (∑ i ∈ t, x i) y = ∑ i ∈ t, f (x i) y :=
  _root_.map_sum (flip f y) _ _

/-- Restricting a bilinear map in the second entry -/
/-
**LinearMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ->ₛₗ[σ₁₂] M₂
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting a bilinear map in the second entry
-/
def domRestrict₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : Submodule S N) : M →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P where
  toFun m := (f m).domRestrict q
  map_add' m₁ m₂ := LinearMap.ext fun _ => by simp only [map_add, domRestrict_apply, add_apply]
  map_smul' c m :=
    LinearMap.ext fun _ => by simp only [f.map_smulₛₗ, domRestrict_apply, smul_apply]
/-
**LinearMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ->ₛₗ[σ₁₂] M₂
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict₂_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (q : Submodule S N) (x : M) (y : q) :
    f.domRestrict₂ q x y = f x y := rfl

/-- Restricting a bilinear map in both components -/
/-
**LinearMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ->ₛₗ[σ₁₂] M₂
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting a bilinear map in both components
-/
def domRestrict₁₂ (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N) :
    p →ₛₗ[ρ₁₂] q →ₛₗ[σ₁₂] P :=
  (f.domRestrict p).domRestrict₂ q
/-
**LinearMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ->ₛₗ[σ₁₂] M₂
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict₁₂_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N)
    (x : p) (y : q) : f.domRestrict₁₂ p q x y = f x y := rfl

section restrictScalars

variable (R' S' : Type*)
variable [Semiring R'] [Semiring S'] [Module R' M] [Module S' N] [Module R' Pₗ] [Module S' Pₗ]
variable [SMulCommClass S' R' Pₗ]
variable [SMul S' S] [IsScalarTower S' S N] [IsScalarTower S' S Pₗ]
variable [SMul R' R] [IsScalarTower R' R M] [IsScalarTower R' R Pₗ]

/-- If `B : M → N → Pₗ` is `R`-`S` bilinear and `R'` and `S'` are compatible scalar multiplications,
then the restriction of scalars is a `R'`-`S'` bilinear map. -/
@[simps!]
/-
**LinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_1) →   {S : Type u_5} →     {M : Type u_8} →       {M₂ : Type 
u_10} →         [inst : Semiring R] →           [inst_1 : Semiring S] →         
    [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M₂] →    
             [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.M
odule R M₂] →                     [inst_6 : _root_.Module S M] →                
       [inst_7 : _root_.Module S M₂] → [LinearMap.CompatibleSMul M M₂ R S] → (M 
→ₗ[S] M₂) → M →ₗ[R] M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B : M → N → Pₗ` is `R`-`S` bilinear and `R'` and `S'` are compatible scalar 
multiplications,
then the restriction of scalars is a `R'`-`S'` bilinear map.
-/
def restrictScalars₁₂ (B : M →ₗ[R] N →ₗ[S] Pₗ) : M →ₗ[R'] N →ₗ[S'] Pₗ :=
  LinearMap.mk₂' R' S'
    (B · ·)
    B.map_add₂
    (fun r' m _ ↦ by
      rw [← smul_one_smul R r' m, map_smul₂, smul_one_smul])
    (fun _ ↦ map_add _)
    (fun _ x ↦ (B x).map_smul_of_tower _)
/-
**LinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_1) →   {S : Type u_5} →     {M : Type u_8} →       {M₂ : Type 
u_10} →         [inst : Semiring R] →           [inst_1 : Semiring S] →         
    [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M₂] →    
             [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.M
odule R M₂] →                     [inst_6 : _root_.Module S M] →                
       [inst_7 : _root_.Module S M₂] → [LinearMap.CompatibleSMul M M₂ R S] → (M 
→ₗ[S] M₂) → M →ₗ[R] M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars₁₂_injective : Function.Injective
    (LinearMap.restrictScalars₁₂ R' S' : (M →ₗ[R] N →ₗ[S] Pₗ) → (M →ₗ[R'] N →ₗ[S'] Pₗ)) :=
  fun _ _ h ↦ ext₂ (congr_fun₂ h :)

@[simp]
/-
**LinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_1) →   {S : Type u_5} →     {M : Type u_8} →       {M₂ : Type 
u_10} →         [inst : Semiring R] →           [inst_1 : Semiring S] →         
    [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M₂] →    
             [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.M
odule R M₂] →                     [inst_6 : _root_.Module S M] →                
       [inst_7 : _root_.Module S M₂] → [LinearMap.CompatibleSMul M M₂ R S] → (M 
→ₗ[S] M₂) → M →ₗ[R] M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars₁₂_inj {B B' : M →ₗ[R] N →ₗ[S] Pₗ} :
    B.restrictScalars₁₂ R' S' = B'.restrictScalars₁₂ R' S' ↔ B = B' :=
  (restrictScalars₁₂_injective R' S').eq_iff

end restrictScalars

/-- `LinearMap.flip` as an isomorphism of modules. -/
/-
**LinearMap.lflip** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lflip {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SM
ulCommClass R₂ R₀ P] : (M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) ≃ₗ[R₀] (N ->ₛₗ[σ₁₂] M ->ₛₗ[ρ₁
₂] P) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.flip` as an isomorphism of modules.
-/
def lflip {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SMulCommClass R₂ R₀ P] :
    (M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) ≃ₗ[R₀] (N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P) where
  toFun := flip
  invFun := flip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
/-
**LinearMap.lflip_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {S : Type u_3} {S₂ : Type u_4} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : Semiring S] [inst_3 : Semiring S₂] 
{M : Type u_5} {N : Type u_7} {P : Type u_9} [inst_4 : AddCommMonoid M]   [inst_
5 : AddCommMonoid N] [inst_6 : AddCommMonoid P] [inst_7 : _root_.Module R M] [in
st_8 : _root_.Module S N]   [inst_9 : _root_.Module R₂ P] [inst_10 : _root_.Modu
le S₂ P] [inst_11 : SMulCommClass S₂ R₂ P] {ρ₁₂ : R →+* R₂}   {σ₁₂ : S →+* S₂} {
R₀ : Type u_14} [inst_12 : Semiring R₀] [inst_13 : _root_.Module R₀ P]   [inst_1
4 : SMulCommClass S₂ R₀ P] [inst_15 : SMulCommClass R₂ R₀ P], LinearMap.lflip.sy
mm = LinearMap.lflip
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
@[simp] theorem lflip_symm
    {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SMulCommClass R₂ R₀ P] :
    (lflip : (M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) ≃ₗ[R₀] (N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P)).symm = lflip :=
  rfl

@[simp]
/-
**LinearMap.lflip_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lflip_apply {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ 
P] [SMulCommClass R₂ R₀ P] (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : lflip (R₀
参数：f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem lflip_apply {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P]
    [SMulCommClass R₂ R₀ P] (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) :
    lflip (R₀ := R₀) f = f.flip := rfl

end Semiring

section CommSemiring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {A R R₁ R₂ : Type*} [Semiring A] [CommSemiring R] [Semiring R₁] [Semiring R₂]
variable {M Mₗ N Nₗ Pₗ Qₗ Qₗ' : Type*} [AddCommMonoid M] [AddCommMonoid Mₗ] [AddCommMonoid N]
variable [AddCommMonoid Nₗ] [AddCommMonoid Pₗ] [AddCommMonoid Qₗ] [AddCommMonoid Qₗ']
variable [Module R M] [Module R Mₗ] [Module R₁ Mₗ] [Module R₂ N] [Module R Nₗ] [Module R Pₗ]
variable [Module R₂ Pₗ] [Module R₁ Pₗ] [Module R Qₗ] [Module R₁ Qₗ] [Module R Qₗ'] [Module R₂ Qₗ']
variable {Tₗ Tₗ' : Type*} [AddCommMonoid Tₗ] [AddCommMonoid Tₗ'] [Module R₁ Tₗ] [Module R₂ Tₗ']

variable (R)

/-- Create a bilinear map from a function that is linear in each component.

This is a shorthand for `mk₂'` for the common case when `R = S`. -/
/-
**LinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_16} →         
    {M₂ : Type u_17} →               [inst_2 : AddCommMonoid M] →               
  [inst_3 : AddCommMonoid M₂] →                   [inst_4 : _root_.Module R M] →
                     [inst_5 : _root_.Module S M₂] →                       (toAd
dHom : M →ₙ+ M₂) →                         (∀ (m : R) (x : M), toAddHom.toFun (m
 • x) = σ m • toAddHom.toFun x) → M →ₛₗ[σ] M₂
参数：toAddHom : M →ₙ+ M₂；∀ (m : R) (x : M), toAddHom.toFun (m • x) = σ m • toAddHo
m.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a bilinear map from a function that is linear in each component.

This is a shorthand for `mk₂'` for the common case when `R = S`.
-/
def mk₂ (f : M → Nₗ → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : R) (m n), f m (c • n) = c • f m n) : M →ₗ[R] Nₗ →ₗ[R] Pₗ :=
  mk₂' R R f H1 H2 H3 H4

@[simp]
/-
**LinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {M : Type u_16} →         
    {M₂ : Type u_17} →               [inst_2 : AddCommMonoid M] →               
  [inst_3 : AddCommMonoid M₂] →                   [inst_4 : _root_.Module R M] →
                     [inst_5 : _root_.Module S M₂] →                       (toAd
dHom : M →ₙ+ M₂) →                         (∀ (m : R) (x : M), toAddHom.toFun (m
 • x) = σ m • toAddHom.toFun x) → M →ₛₗ[σ] M₂
参数：toAddHom : M →ₙ+ M₂；∀ (m : R) (x : M), toAddHom.toFun (m • x) = σ m • toAddHo
m.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk₂_apply (f : M → Nₗ → Pₗ) {H1 H2 H3 H4} (m : M) (n : Nₗ) :
    (mk₂ R f H1 H2 H3 H4 : M →ₗ[R] Nₗ →ₗ[R] Pₗ) m n = f m n := rfl

variable [Module A Pₗ] [SMulCommClass R A Pₗ] {R}

/-- Composing linear maps `Q → M` and `Q' → N` with a bilinear map `M → N → P` to
form a bilinear map `Q → Q' → P`. -/
/-
**LinearMap.compl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing linear maps `Q → M` and `Q' → N` with a bilinear map `M → N → P` to
form a bilinear map `Q → Q' → P`.
-/
def compl₁₂ [SMulCommClass R₂ R₁ Pₗ]
    (f : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) (g : Qₗ →ₗ[R₁] Mₗ) (g' : Qₗ' →ₗ[R₂] N) :
    Qₗ →ₗ[R₁] Qₗ' →ₗ[R₂] Pₗ :=
  (f.comp g).compl₂ g'

@[simp]
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₁₂_apply [SMulCommClass R₂ R₁ Pₗ]
    (f : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) (g : Qₗ →ₗ[R₁] Mₗ) (g' : Qₗ' →ₗ[R₂] N) (x : Qₗ)
    (y : Qₗ') : f.compl₁₂ g g' x y = f (g x) (g' y) := rfl

@[simp]
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₁₂_id_id [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) :
    f.compl₁₂ LinearMap.id LinearMap.id = f := by
  ext
  simp_rw [compl₁₂_apply, id_coe, _root_.id]
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₁₂_comp_left [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) (g : Qₗ →ₗ[R₁] Mₗ)
    (g' : Qₗ' →ₗ[R₂] N) (h : Tₗ →ₗ[R₁] Qₗ) : f.compl₁₂ (g ∘ₗ h) g' = (f.compl₁₂ g g') ∘ₗ h := rfl
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₁₂_comp_right [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) (g : Qₗ →ₗ[R₁] Mₗ)
    (g' : Qₗ' →ₗ[R₂] N) (h' : Tₗ' →ₗ[R₂] Qₗ') :
    f.compl₁₂ g (g' ∘ₗ h') = (f.compl₁₂ g g').compl₂ h' := rfl
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₁₂_comp_comp [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) (g : Qₗ →ₗ[R₁] Mₗ)
    (g' : Qₗ' →ₗ[R₂] N) (h : Tₗ →ₗ[R₁] Qₗ) (h' : Tₗ' →ₗ[R₂] Qₗ') :
    f.compl₁₂ (g ∘ₗ h) (g' ∘ₗ h') = (f.compl₁₂ g g').compl₁₂ h h' := rfl
/-
**LinearMap.compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₁₂_inj [SMulCommClass R₂ R₁ Pₗ]
    {f₁ f₂ : Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ} {g : Qₗ →ₗ[R₁] Mₗ} {g' : Qₗ' →ₗ[R₂] N}
    (hₗ : Function.Surjective g) (hᵣ : Function.Surjective g') :
    f₁.compl₁₂ g g' = f₂.compl₁₂ g g' ↔ f₁ = f₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    convert! LinearMap.congr_fun₂ h x' y' using 0
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h; rfl

omit [Module R M] in
/-- Composing a linear map `P → Q` and a bilinear map `M → N → P` to
form a bilinear map `M → N → Q`.

See `LinearMap.compr₂ₛₗ` for a version of this which does not support towers of scalars but which
does support semi-linear maps. -/
/-
**LinearMap.compr** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a linear map `P → Q` and a bilinear map `M → N → P` to
form a bilinear map `M → N → Q`.

See `LinearMap.compr₂ₛₗ` for a version of this which does not support towers of 
scalars but which
does support semi-linear maps.
-/
def compr₂ [Module R A] [Module A M] [Module A Qₗ]
    [SMulCommClass R A Qₗ] [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ]
    (f : M →ₗ[A] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[A] Qₗ) : M →ₗ[A] Nₗ →ₗ[R] Qₗ where
  toFun x := g.restrictScalars R ∘ₗ (f x)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Module R M] in
@[simp]
/-
**LinearMap.compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂_apply [Module R A] [Module A M] [Module A Qₗ]
    [SMulCommClass R A Qₗ] [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ]
    (f : M →ₗ[A] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[A] Qₗ) (m : M) (n : Nₗ) :
    f.compr₂ g m n = g (f m n) := rfl

omit [Module R M] in
@[simp]
/-
**LinearMap.compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂_id [Module R A] [Module A M] [IsScalarTower R A Pₗ] (f : M →ₗ[A] Nₗ →ₗ[R] Pₗ) :
    f.compr₂ LinearMap.id = f := rfl

omit [Module R M] in
/-
**LinearMap.compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂_comp {Tₗ : Type*} [AddCommMonoid Tₗ] [Module R Tₗ] [Module A Tₗ] [Module R A]
    [Module A M] [Module A Qₗ] [SMulCommClass R A Qₗ] [SMulCommClass R A Tₗ]
    [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ] [IsScalarTower R A Tₗ]
    (f : M →ₗ[A] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[A] Qₗ) (h : Qₗ →ₗ[A] Tₗ) :
    f.compr₂ (h ∘ₗ g) = (f.compr₂ g).compr₂ h := rfl

/-- A version of `Function.Injective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.injective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Injective.comp` for composition of a bilinear map with a 
linear map.
-/
theorem injective_compr₂_of_injective (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ) (hf : Injective f)
    (hg : Injective g) : Injective (f.compr₂ g) :=
  hg.injective_linearMapComp_left.comp hf

/-- A version of `Function.Surjective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.surjective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Surjective.comp` for composition of a bilinear map with a
 linear map.
-/
theorem surjective_compr₂_of_exists_rightInverse (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ →ₗ[R] Qₗ)
    (hf : Surjective f) (hg : ∃ g' : Qₗ →ₗ[R] Pₗ, g.comp g' = LinearMap.id) :
    Surjective (f.compr₂ g) := (surjective_comp_left_of_exists_rightInverse hg).comp hf

/-- A version of `Function.Surjective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.surjective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Surjective.comp` for composition of a bilinear map with a
 linear map.
-/
theorem surjective_compr₂_of_equiv (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Surjective f) :
    Surjective (f.compr₂ g.toLinearMap) :=
  surjective_compr₂_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

/-- A version of `Function.Bijective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.bijective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Bijective.comp` for composition of a bilinear map with a 
linear map.
-/
theorem bijective_compr₂_of_equiv (f : M →ₗ[R] Nₗ →ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Bijective f) :
    Bijective (f.compr₂ g.toLinearMap) :=
  ⟨injective_compr₂_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂_of_equiv f g hf.2⟩

section CommSemiringSemilinear

variable {R₂ R₃ R₄ M N P Q : Type*}
variable [CommSemiring R₂] [CommSemiring R₃] [CommSemiring R₄]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R₂ N] [Module R₃ P] [Module R₄ Q]
variable {σ₁₂ : R →+* R₂} {σ₁₃ : R →+* R₃} {σ₁₄ : R →+* R₄} {σ₂₃ : R₂ →+* R₃}
variable {σ₂₄ : R₂ →+* R₄} {σ₃₄ : R₃ →+* R₄} {σ₄₂ : R₄ →+* R₂} {σ₄₃ : R₄ →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₄₂ σ₂₃ σ₄₃]
variable [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
variable [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃]

variable (M N P)

variable (R₃) in
/-- Composing linear maps as a bilinear map from `(M →ₛₗ[σ₁₂] N) × (N →ₛₗ[σ₂₃] P)`
to `M →ₛₗ[σ₁₃] P`. -/
/-
**LinearMap.llcomp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：llcomp : (N ->ₛₗ[σ₂₃] P) ->ₗ[R₃] (M ->ₛₗ[σ₁₂] N) ->ₛₗ[σ₂₃] M ->ₛₗ[σ₁₃] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing linear maps as a bilinear map from `(M →ₛₗ[σ₁₂] N) × (N →ₛₗ[σ₂₃] P)`
to `M →ₛₗ[σ₁₃] P`.
-/
def llcomp : (N →ₛₗ[σ₂₃] P) →ₗ[R₃] (M →ₛₗ[σ₁₂] N) →ₛₗ[σ₂₃] M →ₛₗ[σ₁₃] P :=
  flip
    { toFun := lcompₛₗ _ P σ₂₃
      map_add' := fun _f _f' => ext₂ fun g _x => g.map_add _ _
      map_smul' := fun (_c : R₂) _f => ext₂ fun g _x => g.map_smulₛₗ _ _ }

variable {M N P}

@[simp]
/-
**LinearMap.llcomp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：llcomp_apply (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N) (x : M) : llcomp _ M 
N P f g x = f (g x)
参数：f : N ->ₛₗ[σ₂₃] P；g : M ->ₛₗ[σ₁₂] N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem llcomp_apply (f : N →ₛₗ[σ₂₃] P) (g : M →ₛₗ[σ₁₂] N) (x : M) :
    llcomp _ M N P f g x = f (g x) := rfl
/-
**LinearMap.llcomp_apply'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：llcomp_apply' (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N) : llcomp _ M N P f g
 = f ∘ₛₗ g
参数：f : N ->ₛₗ[σ₂₃] P；g : M ->ₛₗ[σ₁₂] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem llcomp_apply' (f : N →ₛₗ[σ₂₃] P) (g : M →ₛₗ[σ₁₂] N) : llcomp _ M N P f g = f ∘ₛₗ g := rfl

omit [Module R M] in
/-- Composing a linear map `P →ₛₗ[σ₃₄] Q` and a bilinear map `M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P` to
form a bilinear map `M →ₛₗ[σ₁₄] N →ₛₗ[σ₂₄] Q`.

See `LinearMap.compr₂` for a version of this definition, which does not support semi-linear maps but
which does support towers of scalars. -/
/-
**LinearMap.compr** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a linear map `P →ₛₗ[σ₃₄] Q` and a bilinear map `M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] 
P` to
form a bilinear map `M →ₛₗ[σ₁₄] N →ₛₗ[σ₂₄] Q`.

See `LinearMap.compr₂` for a version of this definition, which does not support 
semi-linear maps but
which does support towers of scalars.
-/
def compr₂ₛₗ (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) (g : P →ₛₗ[σ₃₄] Q) : M →ₛₗ[σ₁₄] N →ₛₗ[σ₂₄] Q :=
  llcomp _ N P Q g ∘ₛₗ f

@[simp]
/-
**LinearMap.compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂ₛₗ_apply (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) (g : P →ₛₗ[σ₃₄] Q) (m : M) (n : N) :
    f.compr₂ₛₗ g m n = g (f m n) := rfl

@[simp]
/-
**LinearMap.compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂ₛₗ_id (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) : f.compr₂ₛₗ LinearMap.id = f := rfl
/-
**LinearMap.compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂ₛₗ_comp {Q' R₅ : Type*} [CommSemiring R₅] [AddCommMonoid Q'] [Module R₅ Q']
    {σ₁₅ : R →+* R₅} {σ₂₅ : R₂ →+* R₅} {σ₃₅ : R₃ →+* R₅} {σ₄₅ : R₄ →+* R₅}
    [RingHomCompTriple σ₁₃ σ₃₅ σ₁₅] [RingHomCompTriple σ₁₄ σ₄₅ σ₁₅] [RingHomCompTriple σ₂₃ σ₃₅ σ₂₅]
    [RingHomCompTriple σ₂₄ σ₄₅ σ₂₅] [RingHomCompTriple σ₃₄ σ₄₅ σ₃₅] (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P)
    (g : P →ₛₗ[σ₃₄] Q) (h : Q →ₛₗ[σ₄₅] Q') : f.compr₂ₛₗ (h ∘ₛₗ g) = (f.compr₂ₛₗ g).compr₂ₛₗ h := rfl

/-- A version of `Function.Injective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.injective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Injective.comp` for composition of a bilinear map with a 
linear map.
-/
theorem injective_compr₂ₛₗ_of_injective (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) (g : P →ₛₗ[σ₃₄] Q)
    (hf : Injective f) (hg : Injective g) : Injective (f.compr₂ₛₗ g) :=
  hg.injective_linearMapComp_left.comp hf

/-- A version of `Function.Surjective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.surjective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Surjective.comp` for composition of a bilinear map with a
 linear map.
-/
theorem surjective_compr₂ₛₗ_of_exists_rightInverse [RingHomInvPair σ₃₄ σ₄₃]
    (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) (g : P →ₛₗ[σ₃₄] Q)
    (hf : Surjective f) (hg : ∃ g' : Q →ₛₗ[σ₄₃] P, g.comp g' = LinearMap.id) :
    Surjective (f.compr₂ₛₗ g) := (surjective_comp_left_of_exists_rightInverse hg).comp hf

/-- A version of `Function.Surjective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.surjective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Surjective.comp` for composition of a bilinear map with a
 linear map.
-/
theorem surjective_compr₂ₛₗ_of_equiv [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
    (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) (g : P ≃ₛₗ[σ₃₄] Q) (hf : Surjective f) :
    Surjective (f.compr₂ₛₗ g.toLinearMap) :=
  surjective_compr₂ₛₗ_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

/-- A version of `Function.Bijective.comp` for composition of a bilinear map with a linear map. -/
/-
**LinearMap.bijective_compr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Function.Bijective.comp` for composition of a bilinear map with a 
linear map.
-/
theorem bijective_compr₂ₛₗ_of_equiv [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
    (f : M →ₛₗ[σ₁₃] N →ₛₗ[σ₂₃] P) (g : P ≃ₛₗ[σ₃₄] Q) (hf : Bijective f) :
    Bijective (f.compr₂ₛₗ g.toLinearMap) :=
  ⟨injective_compr₂ₛₗ_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂ₛₗ_of_equiv f g hf.2⟩

end CommSemiringSemilinear

variable (R M)

/-- Scalar multiplication as a bilinear map `R → M → M`. -/
/-
**LinearMap.lsmul** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lsmul : R ->ₗ[R] M ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as a bilinear map `R → M → M`.
-/
def lsmul : R →ₗ[R] M →ₗ[R] M :=
  mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [smul_smul, mul_comm]

variable {R}
/-
**LinearMap.lsmul_eq_distribSMultoLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：lsmul_eq_distribSMultoLinearMap (r : R) : lsmul R M r = DistribSMul.toLine
arMap R M r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lsmul_eq_distribSMultoLinearMap (r : R) :
    lsmul R M r = DistribSMul.toLinearMap R M r := rfl

@[deprecated (since := "2026-01-07")]
alias lsmul_eq_DistribMulAction_toLinearMap := lsmul_eq_distribSMultoLinearMap

variable {M}

@[simp]
/-
**LinearMap.lsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m := rfl

variable (R M Nₗ) in
/-- A shorthand for the type of `R`-bilinear `Nₗ`-valued maps on `M`. -/
/-
**LinearMap.BilinMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_2) →   [inst : CommSemiring R] →     (M : Type u_5) →       (N
ₗ : Type u_8) →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddComm
Monoid Nₗ] → [_root_.Module R M] → [_root_.Module R Nₗ] → Type (max u_8 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for the type of `R`-bilinear `Nₗ`-valued maps on `M`.
-/
protected abbrev BilinMap : Type _ := M →ₗ[R] M →ₗ[R] Nₗ

variable (R M) in
/-- For convenience, a shorthand for the type of bilinear forms from `M` to `R`. -/
@[wikidata Q837924]
/-
**LinearMap.BilinForm** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_2) →   [inst : CommSemiring R] → (M : Type u_5) → [inst_1 : Ad
dCommMonoid M] → [_root_.Module R M] → Type (max u_2 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For convenience, a shorthand for the type of bilinear forms from `M` to `R`.
-/
protected abbrev BilinForm : Type _ := LinearMap.BilinMap R M R

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [IsDomain R]

section AddCommGroup

variable [AddCommGroup M] [Module R M]

/-
**LinearMap.lsmul_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lsmul_injective [IsTorsionFree R M] {x : R} (hx : x != 0) : Function.Injec
tive (lsmul R M x)
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
theorem lsmul_injective [IsTorsionFree R M] {x : R} (hx : x ≠ 0) :
    Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx
/-
**LinearMap.ker_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_lsmul [IsTorsionFree R M] {a : R} (ha : a != 0) : LinearMap.ker (Linea
rMap.lsmul R M a) = ⊥
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `LinearMap.lsmul_injective`：lsmul_injective [IsTorsionFree R M] {x : R} (
hx : x != 0) : Function.Injective (lsmul R M x)
-/
theorem ker_lsmul [IsTorsionFree R M] {a : R} (ha : a ≠ 0) :
    LinearMap.ker (LinearMap.lsmul R M a) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective (LinearMap.lsmul_injective ha)

end AddCommGroup

end CommRing

open Function

section restrictScalarsRange

variable {R S M P M' P' : Type*}
  [Semiring R] [Semiring S] [SMul S R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]
  [Module S M] [Module S P]
  [IsScalarTower S R M] [IsScalarTower S R P]
  [AddCommMonoid M'] [Module S M'] [AddCommMonoid P'] [Module S P']

variable (i : M' →ₗ[S] M) (k : P' →ₗ[S] P) (hk : Injective k)
  (f : M →ₗ[R] P) (hf : ∀ m, f (i m) ∈ LinearMap.range k)

/-- Restrict the scalars and range of a linear map. -/
/-
**LinearMap.restrictScalarsRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：restrictScalarsRange : M' ->ₗ[S] P'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the scalars and range of a linear map.
-/
noncomputable def restrictScalarsRange :
    M' →ₗ[S] P' :=
  ((f.restrictScalars S).comp i).codLift k hk hf

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearMap.restrictScalarsRange_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalarsRange_apply (m : M') : k (restrictScalarsRange i k hk f hf 
m) = f (i m)
参数：m : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_codLift`：comp_codLift : p.comp (f.codLift p hp h) = f
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.restrictScalars_apply`：restrictScalars_apply (fₗ : M ->ₗ[S] M₂
) (x) : restrictScalars R fₗ x = fₗ x
-/
lemma restrictScalarsRange_apply (m : M') :
    k (restrictScalarsRange i k hk f hf m) = f (i m) := by
  have : k (restrictScalarsRange i k hk f hf m) =
      (k ∘ₗ ((f.restrictScalars S).comp i).codLift k hk hf) m :=
    rfl
  rw [this, comp_codLift, comp_apply, restrictScalars_apply]

@[simp]
/-
**LinearMap.eq_restrictScalarsRange_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：eq_restrictScalarsRange_iff (m : M') (p : P') : p = restrictScalarsRange i
 k hk f hf m ↔ k p = f (i m)
参数：m : M'；p : P'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.restrictScalarsRange_apply`：restrictScalarsRange_apply (m : M'
) : k (restrictScalarsRange i k hk f hf m) = f (i m)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_restrictScalarsRange_iff (m : M') (p : P') :
    p = restrictScalarsRange i k hk f hf m ↔ k p = f (i m) := by
  rw [← restrictScalarsRange_apply i k hk f hf m, hk.eq_iff]

@[simp]
/-
**LinearMap.restrictScalarsRange_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap`。
形式化陈述：restrictScalarsRange_apply_eq_zero_iff (m : M') : restrictScalarsRange i k
 hk f hf m = 0 ↔ f (i m) = 0
参数：m : M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `LinearMap.restrictScalarsRange_apply`：restrictScalarsRange_apply (m : M'
) : k (restrictScalarsRange i k hk f hf m) = f (i m)
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
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrictScalarsRange_apply_eq_zero_iff (m : M') :
    restrictScalarsRange i k hk f hf m = 0 ↔ f (i m) = 0 := by
  rw [← hk.eq_iff, restrictScalarsRange_apply, map_zero]

end restrictScalarsRange

section restrictScalarsRange₂

variable {R S M N P M' N' P' : Type*}
  [CommSemiring R] [CommSemiring S] [SMul S R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
  [Module S M] [Module S N] [Module S P]
  [IsScalarTower S R M] [IsScalarTower S R N] [IsScalarTower S R P]
  [AddCommMonoid M'] [Module S M'] [AddCommMonoid N'] [Module S N'] [AddCommMonoid P'] [Module S P']
  [SMulCommClass R S P]

variable (i : M' →ₗ[S] M) (j : N' →ₗ[S] N) (k : P' →ₗ[S] P) (hk : Injective k)
  (B : M →ₗ[R] N →ₗ[R] P) (hB : ∀ m n, B (i m) (j n) ∈ LinearMap.range k)

/-- Restrict the scalars, domains, and range of a bilinear map. -/
/-
**LinearMap.restrictScalarsRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：restrictScalarsRange : M' ->ₗ[S] P'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the scalars, domains, and range of a bilinear map.
-/
noncomputable def restrictScalarsRange₂ :
    M' →ₗ[S] N' →ₗ[S] P' :=
  (((LinearMap.restrictScalarsₗ S R _ _ _).comp
    (B.restrictScalars S)).compl₁₂ i j).codRestrict₂ k hk hB

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.restrictScalarsRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：restrictScalarsRange : M' ->ₗ[S] P'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restrictScalarsRange₂_apply (m : M') (n : N') :
    k (restrictScalarsRange₂ i j k hk B hB m n) = B (i m) (j n) := by
  simp [restrictScalarsRange₂]

@[simp]
/-
**LinearMap.eq_restrictScalarsRange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_restrictScalarsRange₂_iff (m : M') (n : N') (p : P') :
    p = restrictScalarsRange₂ i j k hk B hB m n ↔ k p = B (i m) (j n) := by
  rw [← restrictScalarsRange₂_apply i j k hk B hB m n, hk.eq_iff]

@[simp]
/-
**LinearMap.restrictScalarsRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：restrictScalarsRange : M' ->ₗ[S] P'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalarsRange₂_apply_eq_zero_iff (m : M') (n : N') :
    restrictScalarsRange₂ i j k hk B hB m n = 0 ↔ B (i m) (j n) = 0 := by
  rw [← hk.eq_iff, restrictScalarsRange₂_apply, map_zero]

end restrictScalarsRange₂

end LinearMap

section IsBilinearMap

variable
  (R : Type*) [CommSemiring R]
  {E : Type*} [AddCommMonoid E] [Module R E]
  {F : Type*} [AddCommMonoid F] [Module R F]
  {G : Type*} [AddCommMonoid G] [Module R G]

-- TODO Also make a semi-linear version.
/-- Bundled statement of bilinearity for a function.

The bundled type `E →ₗ[R] F →ₗ[R] G` should be preferred in cases where that can be used.
`IsBilinearMap` can be useful to have `IsBilinearMap (myFunction ..)` as a hypothesis to a
declaration. -/
/-
**IsBilinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     {E : Type u_2} →       [i
nst_1 : AddCommMonoid E] →         [_root_.Module R E] →           {F : Type u_3
} →             [inst_3 : AddCommMonoid F] →               [_root_.Module R F] →
                 {G : Type u_4} → [inst_5 : AddCommMonoid G] → [_root_.Module R 
G] → (E → F → G) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled statement of bilinearity for a function.

The bundled type `E →ₗ[R] F →ₗ[R] G` should be preferred in cases where that can
 be used.
`IsBilinearMap` can be useful to have `IsBilinearMap (myFunction ..)` as a hypot
hesis to a
declaration.
-/
structure IsBilinearMap (f : E → F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂) y = f x₁ y + f x₂ y
  smul_left : ∀ (c : R) (x : E) (y : F), f (c • x) y = c • f x y
  add_right : ∀ (x : E) (y₁ y₂ : F), f x (y₁ + y₂) = f x y₁ + f x y₂
  smul_right : ∀ (c : R) (x : E) (y : F), f x (c • y) = c • f x y

variable {R} in
/-- Make a bilinear map from a function and a bundled statement of bilinearity. -/
/-
**IsBilinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBilinearMap.toLinearMap {f : E -> F -> G} (hf : IsBilinearMap R f) : E -
>ₗ[R] F ->ₗ[R] G
参数：hf : IsBilinearMap R f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsBilinearMap.add_left`：∀ {R : Type u_1} [inst : CommSemiring R] {E : Ty
pe u_2} [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module R E]   {F : Type u_3}
 [inst_3 : A…
· 使用定理 `IsBilinearMap.smul_left`：∀ {R : Type u_1} [inst : CommSemiring R] {E : T
ype u_2} [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module R E]   {F : Type u_3
} [inst_3 : A…
· 使用定理 `IsBilinearMap.add_right`：∀ {R : Type u_1} [inst : CommSemiring R] {E : T
ype u_2} [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module R E]   {F : Type u_3
} [inst_3 : A…
· 使用定理 `IsBilinearMap.smul_right`：∀ {R : Type u_1} [inst : CommSemiring R] {E : 
Type u_2} [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module R E]   {F : Type u_
3} [inst_3 : A…

--- 原说明 ---
Make a bilinear map from a function and a bundled statement of bilinearity.
-/
def IsBilinearMap.toLinearMap {f : E → F → G} (hf : IsBilinearMap R f) :
    E →ₗ[R] F →ₗ[R] G :=
  LinearMap.mk₂ _ f hf.add_left hf.smul_left hf.add_right hf.smul_right

end IsBilinearMap

