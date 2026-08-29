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
variable {ρ₁₂ : R ->+* R₂} {σ₁₂ : S ->+* S₂}
variable (ρ₁₂ σ₁₂)

-- TODO: refactor to use a structure holding the assumptions, as in `IsBilinearMap` below.
/--
Definition of `mk₂'ₛₗ` / `mk₂'ₛₗ` 的定义

English:
definition mk₂'ₛₗ
  signature: (f : M -> N -> P) (H1 : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  body: { toFun := f m
      map_add' := H3 m
      map_smul' := fun c => H4 c m }
map_add' m₁ m₂ := LinearMap.ext H1 m₁ m₂
map_smul' c m := LinearMap.ext H2 c m

中文:
定义 mk₂'ₛₗ
  签名: (f : M -> N -> P) (H1 : 对任意 m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  定义体: { toFun := f m
      map_add' := H3 m
      map_smul' := fun c => H4 c m }
map_add' m₁ m₂ := LinearMap.ext H1 m₁ m₂
map_smul' c m := LinearMap.ext H2 c m

Depends on / 依赖: LinearMap, LinearMap.ext, map_add, map_smul
-/
def mk₂'ₛₗ (f : M -> N -> P) (H1 : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : forall (c : R) (m n), f (c • m) n = ρ₁₂ c • f m n)
    (H3 : forall m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : forall (c : S) (m n), f m (c • n) = σ₁₂ c • f m n) : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P where
  toFun m :=
    { toFun := f m
      map_add' := H3 m
      map_smul' := fun c => H4 c m }
map_add' m₁ m₂ := LinearMap.ext H1 m₁ m₂
map_smul' c m := LinearMap.ext H2 c m

variable {ρ₁₂ σ₁₂}

@[simp]
/--
theorem `mk₂'ₛₗ_apply` / 定理 `mk₂'ₛₗ_apply`

English:
theorem mk₂'ₛₗ_apply
  given: (f : M -> N -> P) {H1 H2 H3 H4} (m : M) (n : N)
  proof: rfl

中文:
定理 mk₂'ₛₗ_apply
  条件: (f : M -> N -> P) {H1 H2 H3 H4} (m : M) (n : N)
  证明: rfl
-/
theorem mk₂'ₛₗ_apply (f : M -> N -> P) {H1 H2 H3 H4} (m : M) (n : N) :
    (mk₂'ₛₗ ρ₁₂ σ₁₂ f H1 H2 H3 H4 : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) m n = f m n := rfl

variable (R S)

/--
Definition of `mk₂'` / `mk₂'` 的定义

English:
definition mk₂'
  signature: (f : M -> N -> Pₗ) (H1 : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  body: mk₂'ₛₗ (RingHom.id R) (RingHom.id S) f H1 H2 H3 H4

中文:
定义 mk₂'
  签名: (f : M -> N -> Pₗ) (H1 : 对任意 m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  定义体: mk₂'ₛₗ (RingHom.id R) (RingHom.id S) f H1 H2 H3 H4
-/
def mk₂' (f : M -> N -> Pₗ) (H1 : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : forall (c : R) (m n), f (c • m) n = c • f m n)
    (H3 : forall m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : forall (c : S) (m n), f m (c • n) = c • f m n) : M ->ₗ[R] N ->ₗ[S] Pₗ :=
  mk₂'ₛₗ (RingHom.id R) (RingHom.id S) f H1 H2 H3 H4

variable {R S}

@[simp]
/--
theorem `mk₂'_apply` / 定理 `mk₂'_apply`

English:
theorem mk₂'_apply
  given: (f : M -> N -> Pₗ) {H1 H2 H3 H4} (m : M) (n : N)
  proof: rfl

中文:
定理 mk₂'_apply
  条件: (f : M -> N -> Pₗ) {H1 H2 H3 H4} (m : M) (n : N)
  证明: rfl
-/
theorem mk₂'_apply (f : M -> N -> Pₗ) {H1 H2 H3 H4} (m : M) (n : N) :
    (mk₂' R S f H1 H2 H3 H4 : M ->ₗ[R] N ->ₗ[S] Pₗ) m n = f m n := rfl

/--
theorem `ext₂` / 定理 `ext₂`

English:
theorem ext₂
  given: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, f m n = g m n)
  statement: f = g
  proof: LinearMap.ext fun m => LinearMap.ext fun n => H m n

中文:
定理 ext₂
  条件: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : 对任意 m n, f m n = g m n)
  结论: f = g
  证明: LinearMap.ext fun m => LinearMap.ext fun n => H m n

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, f m n = g m n) : f = g :=
  LinearMap.ext fun m => LinearMap.ext fun n => H m n

/--
theorem `congr_fun₂` / 定理 `congr_fun₂`

English:
theorem congr_fun₂
  given: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : f = g) (x y)
  statement: f x y = g x y
  proof: LinearMap.congr_fun (LinearMap.congr_fun h x) y

中文:
定理 congr_fun₂
  条件: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : f = g) (x y)
  结论: f x y = g x y
  证明: LinearMap.congr_fun (LinearMap.congr_fun h x) y

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem congr_fun₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : f = g) (x y) : f x y = g x y :=
  LinearMap.congr_fun (LinearMap.congr_fun h x) y

/--
theorem `ext_iff₂` / 定理 `ext_iff₂`

English:
theorem ext_iff₂
  given: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P}
  statement: f = g ↔ forall m n, f m n = g m n
  proof: ⟨congr_fun₂, ext₂⟩

中文:
定理 ext_iff₂
  条件: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P}
  结论: f = g ↔ 对任意 m n, f m n = g m n
  证明: ⟨congr_fun₂, ext₂⟩
-/
theorem ext_iff₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} : f = g ↔ forall m n, f m n = g m n :=
  ⟨congr_fun₂, ext₂⟩

section

attribute [local instance] SMulCommClass.symm

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
  body: mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun _ _ m => (f m).map_add _ _)
    (fun _ _ m => (f m).map_smulₛₗ _ _)
    (fun n m₁ m₂ => by simp only [map_add, add_apply])
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`.
    -- It looks like we 

中文:
定义 flip
  签名: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
  定义体: mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun _ _ m => (f m).map_add _ _)
    (fun _ _ m => (f m).map_smulₛₗ _ _)
    (fun n m₁ m₂ => by simp only [map_add, add_apply])
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`.
    -- It looks like we 

Depends on / 依赖: add_apply, map_add
-/
def flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : N ->ₛₗ[σ₁₂] M ->ₛₗ[ρ₁₂] P :=
  mk₂'ₛₗ σ₁₂ ρ₁₂ (fun n m => f m n) (fun _ _ m => (f m).map_add _ _)
    (fun _ _ m => (f m).map_smulₛₗ _ _)
    (fun n m₁ m₂ => by simp only [map_add, add_apply])
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`.
    -- It looks like we now run out of assignable metavariables.
    (fun c n m => by simp only [map_smulₛₗ _, smul_apply])

@[simp]
/--
theorem `flip_apply` / 定理 `flip_apply`

English:
theorem flip_apply
  given: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M) (n : N)
  statement: flip f n m = f m n
  proof: rfl

中文:
定理 flip_apply
  条件: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M) (n : N)
  结论: flip f n m = f m n
  证明: rfl
-/
theorem flip_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = f m n := rfl

end

section Semiring

variable {R R₂ R₃ R₄ R₅ : Type*}
variable {M N P Q : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄] [Semiring R₅]
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} {σ₄₂ : R₄ ->+* R₂} {σ₄₃ : R₄ ->+* R₃}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R₂ N] [Module R₃ P] [Module R₄ Q] [Module R₅ P]
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₄₂ σ₂₃ σ₄₃]
variable [SMulCommClass R₃ R₅ P] {σ₁₅ : R ->+* R₅}

variable (R₅ P σ₂₃)

/--
Definition of `lcompₛₗ` / `lcompₛₗ` 的定义

English:
definition lcompₛₗ
  signature: (f : M ->ₛₗ[σ₁₂] N)
  body: letI := SMulCommClass.symm
flip LinearMap.comp (flip id) f

中文:
定义 lcompₛₗ
  签名: (f : M ->ₛₗ[σ₁₂] N)
  定义体: letI := SMulCommClass.symm
flip LinearMap.comp (flip id) f

Depends on / 依赖: LinearMap, LinearMap.comp, SMulCommClass, SMulCommClass.symm
-/
def lcompₛₗ (f : M ->ₛₗ[σ₁₂] N) : (N ->ₛₗ[σ₂₃] P) ->ₗ[R₅] M ->ₛₗ[σ₁₃] P :=
  letI := SMulCommClass.symm
flip LinearMap.comp (flip id) f

variable {P σ₂₃ R₅}

@[simp]
/--
theorem `lcompₛₗ_apply` / 定理 `lcompₛₗ_apply`

English:
theorem lcompₛₗ_apply
  given: (f : M ->ₛₗ[σ₁₂] N) (g : N ->ₛₗ[σ₂₃] P) (x : M)
  proof: rfl

中文:
定理 lcompₛₗ_apply
  条件: (f : M ->ₛₗ[σ₁₂] N) (g : N ->ₛₗ[σ₂₃] P) (x : M)
  证明: rfl
-/
theorem lcompₛₗ_apply (f : M ->ₛₗ[σ₁₂] N) (g : N ->ₛₗ[σ₂₃] P) (x : M) :
    lcompₛₗ R₅ P σ₂₃ f g x = g (f x) := rfl


/--
Definition of `compl₂` / `compl₂` 的定义

English:
definition compl₂
  signature: (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N)
  body: (lcompₛₗ R₅ P σ₂₃ g) (h a)
  map_add' _ _ := by
    simp [map_add]
  map_smul' _ _ := by
    simp [map_smulₛₗ, lcompₛₗ]

@[simp]

中文:
定义 compl₂
  签名: (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N)
  定义体: (lcompₛₗ R₅ P σ₂₃ g) (h a)
  map_add' _ _ := by
    simp [map_add]
  map_smul' _ _ := by
    simp [map_smulₛₗ, lcompₛₗ]

@[simp]
-/
def compl₂ (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N) : M ->ₛₗ[σ₁₅] Q ->ₛₗ[σ₄₃] P where
  toFun a := (lcompₛₗ R₅ P σ₂₃ g) (h a)
  map_add' _ _ := by
    simp [map_add]
  map_smul' _ _ := by
    simp [map_smulₛₗ, lcompₛₗ]

@[simp]
/--
theorem `compl₂_apply` / 定理 `compl₂_apply`

English:
theorem compl₂_apply
  given: (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N) (m : M) (q : Q)
  proof: rfl

@[simp]

中文:
定理 compl₂_apply
  条件: (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N) (m : M) (q : Q)
  证明: rfl

@[simp]
-/
theorem compl₂_apply (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N) (m : M) (q : Q) :
    h.compl₂ g m q = h m (g q) := rfl

@[simp]
/--
theorem `compl₂_id` / 定理 `compl₂_id`

English:
theorem compl₂_id
  given: (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P)
  statement: h.compl₂ LinearMap.id = h
  proof: by
  ext
  rw [compl₂_apply]; rw [id_coe]; rw [_root_.id]

中文:
定理 compl₂_id
  条件: (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P)
  结论: h.compl₂ LinearMap.id = h
  证明: by
  ext
  rw [compl₂_apply]; rw [id_coe]; rw [_root_.id]

Depends on / 依赖: _root_, _root_.id, id_coe
-/
theorem compl₂_id (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) : h.compl₂ LinearMap.id = h := by
  ext
  rw [compl₂_apply]; rw [id_coe]; rw [_root_.id]

/--
theorem `compl₂_comp` / 定理 `compl₂_comp`

English:
theorem compl₂_comp
  statement: {R₆ Q' : Type*} [Semiring R₆] [AddCommMonoid Q'] [Module R₆ Q']
  proof: rfl

中文:
定理 compl₂_comp
  结论: {R₆ Q' : 类型} [Semiring R₆] [AddCommMonoid Q'] [Module R₆ Q']
  证明: rfl
-/
theorem compl₂_comp {R₆ Q' : Type*} [Semiring R₆] [AddCommMonoid Q'] [Module R₆ Q']
    {σ₆₂ : R₆ ->+* R₂} {σ₆₃ : R₆ ->+* R₃} {σ₆₄ : R₆ ->+* R₄}
    [RingHomCompTriple σ₆₂ σ₂₃ σ₆₃] [RingHomCompTriple σ₆₄ σ₄₂ σ₆₂] [RingHomCompTriple σ₆₄ σ₄₃ σ₆₃]
    (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g : Q ->ₛₗ[σ₄₂] N) (f : Q' ->ₛₗ[σ₆₄] Q) :
    h.compl₂ (g ∘ₛₗ f) = (h.compl₂ g).compl₂ f := rfl

end Semiring

section lcomp

variable (S N) [Module R N] [SMulCommClass R S N]

/--
Definition of `lcomp` / `lcomp` 的定义

English:
definition lcomp
  signature: (f : M ->ₗ[R] M₂)
  body: lcompₛₗ _ _ _ f

中文:
定义 lcomp
  签名: (f : M ->ₗ[R] M₂)
  定义体: lcompₛₗ _ _ _ f
-/
def lcomp (f : M ->ₗ[R] M₂) : (M₂ ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] N :=
  lcompₛₗ _ _ _ f

variable {S N}

@[simp]
/--
theorem `lcomp_apply` / 定理 `lcomp_apply`

English:
theorem lcomp_apply
  given: (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N) (x : M)
  statement: lcomp S N f g x = g (f x)
  proof: rfl

中文:
定理 lcomp_apply
  条件: (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N) (x : M)
  结论: lcomp S N f g x = g (f x)
  证明: rfl
-/
theorem lcomp_apply (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N) (x : M) : lcomp S N f g x = g (f x) := rfl

/--
theorem `lcomp_apply'` / 定理 `lcomp_apply'`

English:
theorem lcomp_apply'
  given: (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N)
  statement: lcomp S N f g = g ∘ₗ f
  proof: rfl

中文:
定理 lcomp_apply'
  条件: (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N)
  结论: lcomp S N f g = g ∘ₗ f
  证明: rfl
-/
theorem lcomp_apply' (f : M ->ₗ[R] M₂) (g : M₂ ->ₗ[R] N) : lcomp S N f g = g ∘ₗ f := rfl

/--
lemma `lcomp_injective_of_surjective` / 引理 `lcomp_injective_of_surjective`

English:
lemma lcomp_injective_of_surjective
  given: (g : M ->ₗ[R] M₂) (surj : Function.Surjective g)
  proof: surj.injective_linearMapComp_right

中文:
引理 lcomp_injective_of_surjective
  条件: (g : M ->ₗ[R] M₂) (surj : Function.Surjective g)
  证明: surj.injective_linearMapComp_right

Depends on / 依赖: injective_linearMapComp_right, surj.injective_linearMapComp_right
-/
lemma lcomp_injective_of_surjective (g : M ->ₗ[R] M₂) (surj : Function.Surjective g) :
    Function.Injective (LinearMap.lcomp S N g) :=
  surj.injective_linearMapComp_right

end lcomp

attribute [local instance] SMulCommClass.symm

@[simp]
/--
theorem `flip_flip` / 定理 `flip_flip`

English:
theorem flip_flip
  given: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
  statement: f.flip.flip = f
  proof: LinearMap.ext₂ fun _x _y => (f.flip.flip_apply _ _).trans (f.flip_apply _ _)

中文:
定理 flip_flip
  条件: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
  结论: f.flip.flip = f
  证明: LinearMap.ext₂ fun _x _y => (f.flip.flip_apply _ _).trans (f.flip_apply _ _)

Depends on / 依赖: LinearMap, LinearMap.ext, f.flip.flip_apply, f.flip_apply, flip_apply
-/
theorem flip_flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : f.flip.flip = f :=
  LinearMap.ext₂ fun _x _y => (f.flip.flip_apply _ _).trans (f.flip_apply _ _)

/--
theorem `flip_inj` / 定理 `flip_inj`

English:
theorem flip_inj
  given: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : flip f = flip g)
  statement: f = g
  proof: ext₂ fun m n => show flip f n m = flip g n m by rw [H]

中文:
定理 flip_inj
  条件: {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : flip f = flip g)
  结论: f = g
  证明: ext₂ fun m n => show flip f n m = flip g n m by rw [H]
-/
theorem flip_inj {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : flip f = flip g) : f = g :=
  ext₂ fun m n => show flip f n m = flip g n m by rw [H]

/--
theorem `map_zero₂` / 定理 `map_zero₂`

English:
theorem map_zero₂
  given: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y)
  statement: f 0 y = 0
  proof: (flip f y).map_zero

中文:
定理 map_zero₂
  条件: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y)
  结论: f 0 y = 0
  证明: (flip f y).map_zero

Depends on / 依赖: map_zero
-/
theorem map_zero₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y) : f 0 y = 0 :=
  (flip f y).map_zero

/--
theorem `map_neg₂` / 定理 `map_neg₂`

English:
theorem map_neg₂
  given: (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y)
  statement: f (-x) y = -f x y
  proof: (flip f y).map_neg _

中文:
定理 map_neg₂
  条件: (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y)
  结论: f (-x) y = -f x y
  证明: (flip f y).map_neg _

Depends on / 依赖: map_neg
-/
theorem map_neg₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y) : f (-x) y = -f x y :=
  (flip f y).map_neg _

/--
theorem `map_sub₂` / 定理 `map_sub₂`

English:
theorem map_sub₂
  given: (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z)
  statement: f (x - y) z = f x z - f y z
  proof: (flip f z).map_sub _ _

中文:
定理 map_sub₂
  条件: (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z)
  结论: f (x - y) z = f x z - f y z
  证明: (flip f z).map_sub _ _

Depends on / 依赖: map_sub
-/
theorem map_sub₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z) : f (x - y) z = f x z - f y z :=
  (flip f z).map_sub _ _

/--
theorem `map_add₂` / 定理 `map_add₂`

English:
theorem map_add₂
  given: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y)
  statement: f (x₁ + x₂) y = f x₁ y + f x₂ y
  proof: (flip f y).map_add _ _

中文:
定理 map_add₂
  条件: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y)
  结论: f (x₁ + x₂) y = f x₁ y + f x₂ y
  证明: (flip f y).map_add _ _

Depends on / 依赖: map_add
-/
theorem map_add₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y :=
  (flip f y).map_add _ _

/--
theorem `map_smul₂` / 定理 `map_smul₂`

English:
theorem map_smul₂
  given: (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (x y)
  statement: f (r • x) y = r • f x y
  proof: (flip f y).map_smul _ _

中文:
定理 map_smul₂
  条件: (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (x y)
  结论: f (r • x) y = r • f x y
  证明: (flip f y).map_smul _ _

Depends on / 依赖: map_smul
-/
theorem map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (x y) : f (r • x) y = r • f x y :=
  (flip f y).map_smul _ _

/--
theorem `map_smulₛₗ₂` / 定理 `map_smulₛₗ₂`

English:
theorem map_smulₛₗ₂
  given: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (r : R) (x y)
  statement: f (r • x) y = ρ₁₂ r • f x y
  proof: (flip f y).map_smulₛₗ _ _

中文:
定理 map_smulₛₗ₂
  条件: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (r : R) (x y)
  结论: f (r • x) y = ρ₁₂ r • f x y
  证明: (flip f y).map_smulₛₗ _ _
-/
theorem map_smulₛₗ₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (r : R) (x y) : f (r • x) y = ρ₁₂ r • f x y :=
  (flip f y).map_smulₛₗ _ _

/--
theorem `map_sum₂` / 定理 `map_sum₂`

English:
theorem map_sum₂
  given: {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (t : Finset ι) (x : ι -> M) (y)
  proof: _root_.map_sum (flip f y) _ _

中文:
定理 map_sum₂
  条件: {ι : 类型} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (t : Finset ι) (x : ι -> M) (y)
  证明: _root_.map_sum (flip f y) _ _

Depends on / 依赖: _root_, _root_.map_sum, map_sum
-/
theorem map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (t : Finset ι) (x : ι -> M) (y) :
    f (∑ i in t, x i) y = ∑ i in t, f (x i) y :=
  _root_.map_sum (flip f y) _ _

/--
Definition of `domRestrict₂` / `domRestrict₂` 的定义

English:
definition domRestrict₂
  signature: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (q : Submodule S N)
  body: (f m).domRestrict q
  map_add' m₁ m₂ := LinearMap.ext fun _ => by simp only [map_add, domRestrict_apply, add_apply]
  map_smul' c m :=
    LinearMap.ext fun _ => by simp only [f.map_smulₛₗ, domRestrict_apply, smul_apply]

中文:
定义 domRestrict₂
  签名: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (q : Submodule S N)
  定义体: (f m).domRestrict q
  map_add' m₁ m₂ := LinearMap.ext fun _ => by simp only [map_add, domRestrict_apply, add_apply]
  map_smul' c m :=
    LinearMap.ext fun _ => by simp only [f.map_smulₛₗ, domRestrict_apply, smul_apply]

Depends on / 依赖: domRestrict
-/
def domRestrict₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (q : Submodule S N) : M ->ₛₗ[ρ₁₂] q ->ₛₗ[σ₁₂] P where
  toFun m := (f m).domRestrict q
  map_add' m₁ m₂ := LinearMap.ext fun _ => by simp only [map_add, domRestrict_apply, add_apply]
  map_smul' c m :=
    LinearMap.ext fun _ => by simp only [f.map_smulₛₗ, domRestrict_apply, smul_apply]

/--
theorem `domRestrict₂_apply` / 定理 `domRestrict₂_apply`

English:
theorem domRestrict₂_apply
  given: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (q : Submodule S N) (x : M) (y : q)
  proof: rfl

中文:
定理 domRestrict₂_apply
  条件: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (q : Submodule S N) (x : M) (y : q)
  证明: rfl
-/
theorem domRestrict₂_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (q : Submodule S N) (x : M) (y : q) :
    f.domRestrict₂ q x y = f x y := rfl

/--
Definition of `domRestrict₁₂` / `domRestrict₁₂` 的定义

English:
definition domRestrict₁₂
  signature: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N)
  body: (f.domRestrict p).domRestrict₂ q

中文:
定义 domRestrict₁₂
  签名: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N)
  定义体: (f.domRestrict p).domRestrict₂ q

Depends on / 依赖: domRestrict, f.domRestrict
-/
def domRestrict₁₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N) :
    p ->ₛₗ[ρ₁₂] q ->ₛₗ[σ₁₂] P :=
  (f.domRestrict p).domRestrict₂ q

/--
theorem `domRestrict₁₂_apply` / 定理 `domRestrict₁₂_apply`

English:
theorem domRestrict₁₂_apply
  statement: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N)
  proof: rfl

中文:
定理 domRestrict₁₂_apply
  结论: (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N)
  证明: rfl
-/
theorem domRestrict₁₂_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (p : Submodule R M) (q : Submodule S N)
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
/--
Definition of `restrictScalars₁₂` / `restrictScalars₁₂` 的定义

English:
definition restrictScalars₁₂
  signature: (B : M ->ₗ[R] N ->ₗ[S] Pₗ)
  body: LinearMap.mk₂' R' S'
    (B · ·)
    B.map_add₂
    (fun r' m _ => by
      rw [← smul_one_smul R r' m]; rw [map_smul₂]; rw [smul_one_smul])
    (fun _ => map_add _)
    (fun _ x => (B x).map_smul_of_tower _)

中文:
定义 restrictScalars₁₂
  签名: (B : M ->ₗ[R] N ->ₗ[S] Pₗ)
  定义体: LinearMap.mk₂' R' S'
    (B · ·)
    B.map_add₂
    (fun r' m _ => by
      rw [← smul_one_smul R r' m]; rw [map_smul₂]; rw [smul_one_smul])
    (fun _ => map_add _)
    (fun _ x => (B x).map_smul_of_tower _)

Depends on / 依赖: B.map_add, LinearMap, LinearMap.mk, map_add, map_smul_of_tower, smul_one_smul
-/
def restrictScalars₁₂ (B : M ->ₗ[R] N ->ₗ[S] Pₗ) : M ->ₗ[R'] N ->ₗ[S'] Pₗ :=
  LinearMap.mk₂' R' S'
    (B · ·)
    B.map_add₂
    (fun r' m _ => by
      rw [← smul_one_smul R r' m]; rw [map_smul₂]; rw [smul_one_smul])
    (fun _ => map_add _)
    (fun _ x => (B x).map_smul_of_tower _)

/--
theorem `restrictScalars₁₂_injective` / 定理 `restrictScalars₁₂_injective`

English:
theorem restrictScalars₁₂_injective
  statement: Function.Injective
  proof: fun _ _ h => ext₂ (congr_fun₂ h :)

@[simp]

中文:
定理 restrictScalars₁₂_injective
  结论: Function.Injective
  证明: fun _ _ h => ext₂ (congr_fun₂ h :)

@[simp]
-/
theorem restrictScalars₁₂_injective : Function.Injective
    (LinearMap.restrictScalars₁₂ R' S' : (M ->ₗ[R] N ->ₗ[S] Pₗ) -> (M ->ₗ[R'] N ->ₗ[S'] Pₗ)) :=
  fun _ _ h => ext₂ (congr_fun₂ h :)

@[simp]
/--
theorem `restrictScalars₁₂_inj` / 定理 `restrictScalars₁₂_inj`

English:
theorem restrictScalars₁₂_inj
  given: {B B' : M ->ₗ[R] N ->ₗ[S] Pₗ}
  proof: (restrictScalars₁₂_injective R' S').eq_iff

中文:
定理 restrictScalars₁₂_inj
  条件: {B B' : M ->ₗ[R] N ->ₗ[S] Pₗ}
  证明: (restrictScalars₁₂_injective R' S').eq_iff

Depends on / 依赖: eq_iff
-/
theorem restrictScalars₁₂_inj {B B' : M ->ₗ[R] N ->ₗ[S] Pₗ} :
    B.restrictScalars₁₂ R' S' = B'.restrictScalars₁₂ R' S' ↔ B = B' :=
  (restrictScalars₁₂_injective R' S').eq_iff

end restrictScalars

/--
Definition of `lflip` / `lflip` 的定义

English:
definition lflip
  signature: {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SMulCommClass R₂ R₀ P]
  body: flip
  invFun := flip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 lflip
  签名: {R₀ : 类型} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SMulCommClass R₂ R₀ P]
  定义体: flip
  invFun := flip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
-/
def lflip {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SMulCommClass R₂ R₀ P] :
    (M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) ≃ₗ[R₀] (N ->ₛₗ[σ₁₂] M ->ₛₗ[ρ₁₂] P) where
  toFun := flip
  invFun := flip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/--
theorem `lflip_symm` / 定理 `lflip_symm`

English:
theorem lflip_symm
  proof: rfl

@[simp]

中文:
定理 lflip_symm
  证明: rfl

@[simp]
-/
@[simp] theorem lflip_symm
    {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P] [SMulCommClass R₂ R₀ P] :
    (lflip : (M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) ≃ₗ[R₀] (N ->ₛₗ[σ₁₂] M ->ₛₗ[ρ₁₂] P)).symm = lflip :=
  rfl

@[simp]
/--
theorem `lflip_apply` / 定理 `lflip_apply`

English:
theorem lflip_apply
  statement: {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P]
  proof: rfl

中文:
定理 lflip_apply
  结论: {R₀ : 类型} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P]
  证明: rfl

Depends on / 依赖: f.flip
-/
theorem lflip_apply {R₀ : Type*} [Semiring R₀] [Module R₀ P] [SMulCommClass S₂ R₀ P]
    [SMulCommClass R₂ R₀ P] (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) :
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

/--
Definition of `mk₂` / `mk₂` 的定义

English:
definition mk₂
  signature: (f : M -> Nₗ -> Pₗ) (H1 : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  body: mk₂' R R f H1 H2 H3 H4

@[simp]

中文:
定义 mk₂
  签名: (f : M -> Nₗ -> Pₗ) (H1 : 对任意 m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  定义体: mk₂' R R f H1 H2 H3 H4

@[simp]
-/
def mk₂ (f : M -> Nₗ -> Pₗ) (H1 : forall m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : forall (c : R) (m n), f (c • m) n = c • f m n)
    (H3 : forall m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : forall (c : R) (m n), f m (c • n) = c • f m n) : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ :=
  mk₂' R R f H1 H2 H3 H4

@[simp]
/--
theorem `mk₂_apply` / 定理 `mk₂_apply`

English:
theorem mk₂_apply
  given: (f : M -> Nₗ -> Pₗ) {H1 H2 H3 H4} (m : M) (n : Nₗ)
  proof: rfl

中文:
定理 mk₂_apply
  条件: (f : M -> Nₗ -> Pₗ) {H1 H2 H3 H4} (m : M) (n : Nₗ)
  证明: rfl
-/
theorem mk₂_apply (f : M -> Nₗ -> Pₗ) {H1 H2 H3 H4} (m : M) (n : Nₗ) :
    (mk₂ R f H1 H2 H3 H4 : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) m n = f m n := rfl

variable [Module A Pₗ] [SMulCommClass R A Pₗ] {R}

/--
Definition of `compl₁₂` / `compl₁₂` 的定义

English:
definition compl₁₂
  signature: [SMulCommClass R₂ R₁ Pₗ]
  body: (f.comp g).compl₂ g'

@[simp]

中文:
定义 compl₁₂
  签名: [SMulCommClass R₂ R₁ Pₗ]
  定义体: (f.comp g).compl₂ g'

@[simp]

Depends on / 依赖: f.comp
-/
def compl₁₂ [SMulCommClass R₂ R₁ Pₗ]
    (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ) (g' : Qₗ' ->ₗ[R₂] N) :
    Qₗ ->ₗ[R₁] Qₗ' ->ₗ[R₂] Pₗ :=
  (f.comp g).compl₂ g'

@[simp]
/--
theorem `compl₁₂_apply` / 定理 `compl₁₂_apply`

English:
theorem compl₁₂_apply
  statement: [SMulCommClass R₂ R₁ Pₗ]
  proof: rfl

@[simp]

中文:
定理 compl₁₂_apply
  结论: [SMulCommClass R₂ R₁ Pₗ]
  证明: rfl

@[simp]
-/
theorem compl₁₂_apply [SMulCommClass R₂ R₁ Pₗ]
    (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ) (g' : Qₗ' ->ₗ[R₂] N) (x : Qₗ)
    (y : Qₗ') : f.compl₁₂ g g' x y = f (g x) (g' y) := rfl

@[simp]
/--
theorem `compl₁₂_id_id` / 定理 `compl₁₂_id_id`

English:
theorem compl₁₂_id_id
  given: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ)
  proof: by
  ext
  simp_rw [compl₁₂_apply, id_coe, _root_.id]

中文:
定理 compl₁₂_id_id
  条件: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ)
  证明: by
  ext
  simp_rw [compl₁₂_apply, id_coe, _root_.id]

Depends on / 依赖: _root_, _root_.id, id_coe, simp_rw
-/
theorem compl₁₂_id_id [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) :
    f.compl₁₂ LinearMap.id LinearMap.id = f := by
  ext
  simp_rw [compl₁₂_apply, id_coe, _root_.id]

/--
theorem `compl₁₂_comp_left` / 定理 `compl₁₂_comp_left`

English:
theorem compl₁₂_comp_left
  statement: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
  proof: rfl

中文:
定理 compl₁₂_comp_left
  结论: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
  证明: rfl
-/
theorem compl₁₂_comp_left [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
    (g' : Qₗ' ->ₗ[R₂] N) (h : Tₗ ->ₗ[R₁] Qₗ) : f.compl₁₂ (g ∘ₗ h) g' = (f.compl₁₂ g g') ∘ₗ h := rfl

/--
theorem `compl₁₂_comp_right` / 定理 `compl₁₂_comp_right`

English:
theorem compl₁₂_comp_right
  statement: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
  proof: rfl

中文:
定理 compl₁₂_comp_right
  结论: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
  证明: rfl
-/
theorem compl₁₂_comp_right [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
    (g' : Qₗ' ->ₗ[R₂] N) (h' : Tₗ' ->ₗ[R₂] Qₗ') :
    f.compl₁₂ g (g' ∘ₗ h') = (f.compl₁₂ g g').compl₂ h' := rfl

/--
theorem `compl₁₂_comp_comp` / 定理 `compl₁₂_comp_comp`

English:
theorem compl₁₂_comp_comp
  statement: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
  proof: rfl

中文:
定理 compl₁₂_comp_comp
  结论: [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
  证明: rfl
-/
theorem compl₁₂_comp_comp [SMulCommClass R₂ R₁ Pₗ] (f : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ) (g : Qₗ ->ₗ[R₁] Mₗ)
    (g' : Qₗ' ->ₗ[R₂] N) (h : Tₗ ->ₗ[R₁] Qₗ) (h' : Tₗ' ->ₗ[R₂] Qₗ') :
    f.compl₁₂ (g ∘ₗ h) (g' ∘ₗ h') = (f.compl₁₂ g g').compl₁₂ h h' := rfl

/--
theorem `compl₁₂_inj` / 定理 `compl₁₂_inj`

English:
theorem compl₁₂_inj
  statement: [SMulCommClass R₂ R₁ Pₗ]
  proof: by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    convert! LinearMap.congr_fun₂ h x' y' using 0
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h; rfl

omit [Module R M] in

中文:
定理 compl₁₂_inj
  结论: [SMulCommClass R₂ R₁ Pₗ]
  证明: by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    convert! LinearMap.congr_fun₂ h x' y' using 0
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h; rfl

omit [Module R M] in

Depends on / 依赖: LinearMap, LinearMap.congr_fun, convert
-/
theorem compl₁₂_inj [SMulCommClass R₂ R₁ Pₗ]
    {f₁ f₂ : Mₗ ->ₗ[R₁] N ->ₗ[R₂] Pₗ} {g : Qₗ ->ₗ[R₁] Mₗ} {g' : Qₗ' ->ₗ[R₂] N}
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
/--
Definition of `compr₂` / `compr₂` 的定义

English:
definition compr₂
  signature: [Module R A] [Module A M] [Module A Qₗ]
  body: g.restrictScalars R ∘ₗ (f x)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Module R M] in
@[simp]

中文:
定义 compr₂
  签名: [Module R A] [Module A M] [Module A Qₗ]
  定义体: g.restrictScalars R ∘ₗ (f x)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Module R M] in
@[simp]

Depends on / 依赖: g.restrictScalars, restrictScalars
-/
def compr₂ [Module R A] [Module A M] [Module A Qₗ]
    [SMulCommClass R A Qₗ] [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ]
    (f : M ->ₗ[A] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[A] Qₗ) : M ->ₗ[A] Nₗ ->ₗ[R] Qₗ where
  toFun x := g.restrictScalars R ∘ₗ (f x)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

omit [Module R M] in
@[simp]
/--
theorem `compr₂_apply` / 定理 `compr₂_apply`

English:
theorem compr₂_apply
  statement: [Module R A] [Module A M] [Module A Qₗ]
  proof: rfl

omit [Module R M] in
@[simp]

中文:
定理 compr₂_apply
  结论: [Module R A] [Module A M] [Module A Qₗ]
  证明: rfl

omit [Module R M] in
@[simp]
-/
theorem compr₂_apply [Module R A] [Module A M] [Module A Qₗ]
    [SMulCommClass R A Qₗ] [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ]
    (f : M ->ₗ[A] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[A] Qₗ) (m : M) (n : Nₗ) :
    f.compr₂ g m n = g (f m n) := rfl

omit [Module R M] in
@[simp]
/--
theorem `compr₂_id` / 定理 `compr₂_id`

English:
theorem compr₂_id
  given: [Module R A] [Module A M] [IsScalarTower R A Pₗ] (f : M ->ₗ[A] Nₗ ->ₗ[R] Pₗ)
  proof: rfl

omit [Module R M] in

中文:
定理 compr₂_id
  条件: [Module R A] [Module A M] [IsScalarTower R A Pₗ] (f : M ->ₗ[A] Nₗ ->ₗ[R] Pₗ)
  证明: rfl

omit [Module R M] in
-/
theorem compr₂_id [Module R A] [Module A M] [IsScalarTower R A Pₗ] (f : M ->ₗ[A] Nₗ ->ₗ[R] Pₗ) :
    f.compr₂ LinearMap.id = f := rfl

omit [Module R M] in
/--
theorem `compr₂_comp` / 定理 `compr₂_comp`

English:
theorem compr₂_comp
  statement: {Tₗ : Type*} [AddCommMonoid Tₗ] [Module R Tₗ] [Module A Tₗ] [Module R A]
  proof: rfl

中文:
定理 compr₂_comp
  结论: {Tₗ : 类型} [AddCommMonoid Tₗ] [Module R Tₗ] [Module A Tₗ] [Module R A]
  证明: rfl
-/
theorem compr₂_comp {Tₗ : Type*} [AddCommMonoid Tₗ] [Module R Tₗ] [Module A Tₗ] [Module R A]
    [Module A M] [Module A Qₗ] [SMulCommClass R A Qₗ] [SMulCommClass R A Tₗ]
    [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ] [IsScalarTower R A Tₗ]
    (f : M ->ₗ[A] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[A] Qₗ) (h : Qₗ ->ₗ[A] Tₗ) :
    f.compr₂ (h ∘ₗ g) = (f.compr₂ g).compr₂ h := rfl

/--
theorem `injective_compr₂_of_injective` / 定理 `injective_compr₂_of_injective`

English:
theorem injective_compr₂_of_injective
  statement: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[R] Qₗ) (hf : Injective f)
  proof: hg.injective_linearMapComp_left.comp hf

中文:
定理 injective_compr₂_of_injective
  结论: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[R] Qₗ) (hf : Injective f)
  证明: hg.injective_linearMapComp_left.comp hf

Depends on / 依赖: hg.injective_linearMapComp_left.comp, injective_linearMapComp_left
-/
theorem injective_compr₂_of_injective (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[R] Qₗ) (hf : Injective f)
    (hg : Injective g) : Injective (f.compr₂ g) :=
  hg.injective_linearMapComp_left.comp hf

/--
theorem `surjective_compr₂_of_exists_rightInverse` / 定理 `surjective_compr₂_of_exists_rightInverse`

English:
theorem surjective_compr₂_of_exists_rightInverse
  statement: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[R] Qₗ)
  proof: (surjective_comp_left_of_exists_rightInverse hg).comp hf

中文:
定理 surjective_compr₂_of_exists_rightInverse
  结论: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[R] Qₗ)
  证明: (surjective_comp_left_of_exists_rightInverse hg).comp hf

Depends on / 依赖: surjective_comp_left_of_exists_rightInverse
-/
theorem surjective_compr₂_of_exists_rightInverse (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ->ₗ[R] Qₗ)
    (hf : Surjective f) (hg : exists g' : Qₗ ->ₗ[R] Pₗ, g.comp g' = LinearMap.id) :
    Surjective (f.compr₂ g) := (surjective_comp_left_of_exists_rightInverse hg).comp hf

/--
theorem `surjective_compr₂_of_equiv` / 定理 `surjective_compr₂_of_equiv`

English:
theorem surjective_compr₂_of_equiv
  given: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Surjective f)
  proof: surjective_compr₂_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

中文:
定理 surjective_compr₂_of_equiv
  条件: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Surjective f)
  证明: surjective_compr₂_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

Depends on / 依赖: g.symm, g.toLinearMap, toLinearMap
-/
theorem surjective_compr₂_of_equiv (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Surjective f) :
    Surjective (f.compr₂ g.toLinearMap) :=
  surjective_compr₂_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

/--
theorem `bijective_compr₂_of_equiv` / 定理 `bijective_compr₂_of_equiv`

English:
theorem bijective_compr₂_of_equiv
  given: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Bijective f)
  proof: ⟨injective_compr₂_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂_of_equiv f g hf.2⟩

中文:
定理 bijective_compr₂_of_equiv
  条件: (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Bijective f)
  证明: ⟨injective_compr₂_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂_of_equiv f g hf.2⟩

Depends on / 依赖: bijective, g.bijective, g.toLinearMap, toLinearMap
-/
theorem bijective_compr₂_of_equiv (f : M ->ₗ[R] Nₗ ->ₗ[R] Pₗ) (g : Pₗ ≃ₗ[R] Qₗ) (hf : Bijective f) :
    Bijective (f.compr₂ g.toLinearMap) :=
  ⟨injective_compr₂_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂_of_equiv f g hf.2⟩

section CommSemiringSemilinear

variable {R₂ R₃ R₄ M N P Q : Type*}
variable [CommSemiring R₂] [CommSemiring R₃] [CommSemiring R₄]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R₂ N] [Module R₃ P] [Module R₄ Q]
variable {σ₁₂ : R ->+* R₂} {σ₁₃ : R ->+* R₃} {σ₁₄ : R ->+* R₄} {σ₂₃ : R₂ ->+* R₃}
variable {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} {σ₄₂ : R₄ ->+* R₂} {σ₄₃ : R₄ ->+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₄₂ σ₂₃ σ₄₃]
variable [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
variable [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃]

variable (M N P)

variable (R₃) in
/--
Definition of `llcomp` / `llcomp` 的定义

English:
definition llcomp
  signature: : (N ->ₛₗ[σ₂₃] P) ->ₗ[R₃] (M ->ₛₗ[σ₁₂] N) ->ₛₗ[σ₂₃] M ->ₛₗ[σ₁₃] P
  body: flip
    { toFun := lcompₛₗ _ P σ₂₃
      map_add' := fun _f _f' => ext₂ fun g _x => g.map_add _ _
      map_smul' := fun (_c : R₂) _f => ext₂ fun g _x => g.map_smulₛₗ _ _ }

中文:
定义 llcomp
  签名: : (N ->ₛₗ[σ₂₃] P) ->ₗ[R₃] (M ->ₛₗ[σ₁₂] N) ->ₛₗ[σ₂₃] M ->ₛₗ[σ₁₃] P
  定义体: flip
    { toFun := lcompₛₗ _ P σ₂₃
      map_add' := fun _f _f' => ext₂ fun g _x => g.map_add _ _
      map_smul' := fun (_c : R₂) _f => ext₂ fun g _x => g.map_smulₛₗ _ _ }

Depends on / 依赖: g.map_add, g.map_smul, map_add, map_smul
-/
def llcomp : (N ->ₛₗ[σ₂₃] P) ->ₗ[R₃] (M ->ₛₗ[σ₁₂] N) ->ₛₗ[σ₂₃] M ->ₛₗ[σ₁₃] P :=
  flip
    { toFun := lcompₛₗ _ P σ₂₃
      map_add' := fun _f _f' => ext₂ fun g _x => g.map_add _ _
      map_smul' := fun (_c : R₂) _f => ext₂ fun g _x => g.map_smulₛₗ _ _ }

variable {M N P}

@[simp]
/--
theorem `llcomp_apply` / 定理 `llcomp_apply`

English:
theorem llcomp_apply
  given: (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N) (x : M)
  proof: rfl

中文:
定理 llcomp_apply
  条件: (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N) (x : M)
  证明: rfl
-/
theorem llcomp_apply (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N) (x : M) :
    llcomp _ M N P f g x = f (g x) := rfl

/--
theorem `llcomp_apply'` / 定理 `llcomp_apply'`

English:
theorem llcomp_apply'
  given: (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N)
  statement: llcomp _ M N P f g = f ∘ₛₗ g
  proof: rfl

omit [Module R M] in

中文:
定理 llcomp_apply'
  条件: (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N)
  结论: llcomp _ M N P f g = f ∘ₛₗ g
  证明: rfl

omit [Module R M] in
-/
theorem llcomp_apply' (f : N ->ₛₗ[σ₂₃] P) (g : M ->ₛₗ[σ₁₂] N) : llcomp _ M N P f g = f ∘ₛₗ g := rfl

omit [Module R M] in
/--
Definition of `compr₂ₛₗ` / `compr₂ₛₗ` 的定义

English:
definition compr₂ₛₗ
  signature: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q)
  body: llcomp _ N P Q g ∘ₛₗ f

@[simp]

中文:
定义 compr₂ₛₗ
  签名: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q)
  定义体: llcomp _ N P Q g ∘ₛₗ f

@[simp]

Depends on / 依赖: llcomp
-/
def compr₂ₛₗ (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q) : M ->ₛₗ[σ₁₄] N ->ₛₗ[σ₂₄] Q :=
  llcomp _ N P Q g ∘ₛₗ f

@[simp]
/--
theorem `compr₂ₛₗ_apply` / 定理 `compr₂ₛₗ_apply`

English:
theorem compr₂ₛₗ_apply
  given: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q) (m : M) (n : N)
  proof: rfl

@[simp]

中文:
定理 compr₂ₛₗ_apply
  条件: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q) (m : M) (n : N)
  证明: rfl

@[simp]
-/
theorem compr₂ₛₗ_apply (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q) (m : M) (n : N) :
    f.compr₂ₛₗ g m n = g (f m n) := rfl

@[simp]
/--
theorem `compr₂ₛₗ_id` / 定理 `compr₂ₛₗ_id`

English:
theorem compr₂ₛₗ_id
  given: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P)
  statement: f.compr₂ₛₗ LinearMap.id = f
  proof: rfl

中文:
定理 compr₂ₛₗ_id
  条件: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P)
  结论: f.compr₂ₛₗ LinearMap.id = f
  证明: rfl
-/
theorem compr₂ₛₗ_id (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) : f.compr₂ₛₗ LinearMap.id = f := rfl

/--
theorem `compr₂ₛₗ_comp` / 定理 `compr₂ₛₗ_comp`

English:
theorem compr₂ₛₗ_comp
  statement: {Q' R₅ : Type*} [CommSemiring R₅] [AddCommMonoid Q'] [Module R₅ Q']
  proof: rfl

中文:
定理 compr₂ₛₗ_comp
  结论: {Q' R₅ : 类型} [CommSemiring R₅] [AddCommMonoid Q'] [Module R₅ Q']
  证明: rfl
-/
theorem compr₂ₛₗ_comp {Q' R₅ : Type*} [CommSemiring R₅] [AddCommMonoid Q'] [Module R₅ Q']
    {σ₁₅ : R ->+* R₅} {σ₂₅ : R₂ ->+* R₅} {σ₃₅ : R₃ ->+* R₅} {σ₄₅ : R₄ ->+* R₅}
    [RingHomCompTriple σ₁₃ σ₃₅ σ₁₅] [RingHomCompTriple σ₁₄ σ₄₅ σ₁₅] [RingHomCompTriple σ₂₃ σ₃₅ σ₂₅]
    [RingHomCompTriple σ₂₄ σ₄₅ σ₂₅] [RingHomCompTriple σ₃₄ σ₄₅ σ₃₅] (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P)
    (g : P ->ₛₗ[σ₃₄] Q) (h : Q ->ₛₗ[σ₄₅] Q') : f.compr₂ₛₗ (h ∘ₛₗ g) = (f.compr₂ₛₗ g).compr₂ₛₗ h := rfl

/--
theorem `injective_compr₂ₛₗ_of_injective` / 定理 `injective_compr₂ₛₗ_of_injective`

English:
theorem injective_compr₂ₛₗ_of_injective
  statement: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q)
  proof: hg.injective_linearMapComp_left.comp hf

中文:
定理 injective_compr₂ₛₗ_of_injective
  结论: (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q)
  证明: hg.injective_linearMapComp_left.comp hf

Depends on / 依赖: hg.injective_linearMapComp_left.comp, injective_linearMapComp_left
-/
theorem injective_compr₂ₛₗ_of_injective (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q)
    (hf : Injective f) (hg : Injective g) : Injective (f.compr₂ₛₗ g) :=
  hg.injective_linearMapComp_left.comp hf

/--
theorem `surjective_compr₂ₛₗ_of_exists_rightInverse` / 定理 `surjective_compr₂ₛₗ_of_exists_rightInverse`

English:
theorem surjective_compr₂ₛₗ_of_exists_rightInverse
  statement: [RingHomInvPair σ₃₄ σ₄₃]
  proof: (surjective_comp_left_of_exists_rightInverse hg).comp hf

中文:
定理 surjective_compr₂ₛₗ_of_exists_rightInverse
  结论: [RingHomInvPair σ₃₄ σ₄₃]
  证明: (surjective_comp_left_of_exists_rightInverse hg).comp hf

Depends on / 依赖: surjective_comp_left_of_exists_rightInverse
-/
theorem surjective_compr₂ₛₗ_of_exists_rightInverse [RingHomInvPair σ₃₄ σ₄₃]
    (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ->ₛₗ[σ₃₄] Q)
    (hf : Surjective f) (hg : exists g' : Q ->ₛₗ[σ₄₃] P, g.comp g' = LinearMap.id) :
    Surjective (f.compr₂ₛₗ g) := (surjective_comp_left_of_exists_rightInverse hg).comp hf

/--
theorem `surjective_compr₂ₛₗ_of_equiv` / 定理 `surjective_compr₂ₛₗ_of_equiv`

English:
theorem surjective_compr₂ₛₗ_of_equiv
  statement: [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  proof: surjective_compr₂ₛₗ_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

中文:
定理 surjective_compr₂ₛₗ_of_equiv
  结论: [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  证明: surjective_compr₂ₛₗ_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

Depends on / 依赖: g.symm, g.toLinearMap, toLinearMap
-/
theorem surjective_compr₂ₛₗ_of_equiv [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
    (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ≃ₛₗ[σ₃₄] Q) (hf : Surjective f) :
    Surjective (f.compr₂ₛₗ g.toLinearMap) :=
  surjective_compr₂ₛₗ_of_exists_rightInverse f g.toLinearMap hf ⟨g.symm, by simp⟩

/--
theorem `bijective_compr₂ₛₗ_of_equiv` / 定理 `bijective_compr₂ₛₗ_of_equiv`

English:
theorem bijective_compr₂ₛₗ_of_equiv
  statement: [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  proof: ⟨injective_compr₂ₛₗ_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂ₛₗ_of_equiv f g hf.2⟩

中文:
定理 bijective_compr₂ₛₗ_of_equiv
  结论: [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  证明: ⟨injective_compr₂ₛₗ_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂ₛₗ_of_equiv f g hf.2⟩

Depends on / 依赖: bijective, g.bijective, g.toLinearMap, toLinearMap
-/
theorem bijective_compr₂ₛₗ_of_equiv [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
    (f : M ->ₛₗ[σ₁₃] N ->ₛₗ[σ₂₃] P) (g : P ≃ₛₗ[σ₃₄] Q) (hf : Bijective f) :
    Bijective (f.compr₂ₛₗ g.toLinearMap) :=
  ⟨injective_compr₂ₛₗ_of_injective f g.toLinearMap hf.1 g.bijective.1,
  surjective_compr₂ₛₗ_of_equiv f g hf.2⟩

end CommSemiringSemilinear

variable (R M)

/--
Definition of `lsmul` / `lsmul` 的定义

English:
definition lsmul
  signature: : R ->ₗ[R] M ->ₗ[R] M
  body: mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [smul_smul, mul_comm]

中文:
定义 lsmul
  签名: : R ->ₗ[R] M ->ₗ[R] M
  定义体: mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [smul_smul, mul_comm]

Depends on / 依赖: add_smul, mul_comm, mul_smul, smul_add, smul_smul
-/
def lsmul : R ->ₗ[R] M ->ₗ[R] M :=
  mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add fun r s m => by
    simp only [smul_smul, mul_comm]

variable {R}

/--
lemma `lsmul_eq_distribSMultoLinearMap` / 引理 `lsmul_eq_distribSMultoLinearMap`

English:
lemma lsmul_eq_distribSMultoLinearMap
  given: (r : R)
  proof: rfl

@[deprecated (since := "2026-01-07")]
alias lsmul_eq_DistribMulAction_toLinearMap := lsmul_eq_distribSMultoLinearMap

中文:
引理 lsmul_eq_distribSMultoLinearMap
  条件: (r : R)
  证明: rfl

@[deprecated (since := "2026-01-07")]
alias lsmul_eq_DistribMulAction_toLinearMap := lsmul_eq_distribSMultoLinearMap
-/
lemma lsmul_eq_distribSMultoLinearMap (r : R) :
    lsmul R M r = DistribSMul.toLinearMap R M r := rfl

@[deprecated (since := "2026-01-07")]
alias lsmul_eq_DistribMulAction_toLinearMap := lsmul_eq_distribSMultoLinearMap

variable {M}

@[simp]
/--
theorem `lsmul_apply` / 定理 `lsmul_apply`

English:
theorem lsmul_apply
  given: (r : R) (m : M)
  statement: lsmul R M r m = r • m
  proof: rfl

中文:
定理 lsmul_apply
  条件: (r : R) (m : M)
  结论: lsmul R M r m = r • m
  证明: rfl
-/
theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m := rfl

variable (R M Nₗ) in
/--
Definition of `BilinMap` / `BilinMap` 的定义

English:
abbreviation BilinMap
  signature: : Type _
  body: M ->ₗ[R] M ->ₗ[R] Nₗ

中文:
缩写 BilinMap
  签名: : Type _
  定义体: M ->ₗ[R] M ->ₗ[R] Nₗ
-/
protected abbrev BilinMap : Type _ := M ->ₗ[R] M ->ₗ[R] Nₗ

variable (R M) in
/-- For convenience, a shorthand for the type of bilinear forms from `M` to `R`. -/
@[wikidata Q837924]
/--
Definition of `BilinForm` / `BilinForm` 的定义

English:
abbreviation BilinForm
  signature: : Type _
  body: LinearMap.BilinMap R M R

中文:
缩写 BilinForm
  签名: : Type _
  定义体: LinearMap.BilinMap R M R
-/
protected abbrev BilinForm : Type _ := LinearMap.BilinMap R M R

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [IsDomain R]

section AddCommGroup

variable [AddCommGroup M] [Module R M]

/--
theorem `lsmul_injective` / 定理 `lsmul_injective`

English:
theorem lsmul_injective
  given: [IsTorsionFree R M] {x : R} (hx : x != 0)
  proof: smul_right_injective _ hx

中文:
定理 lsmul_injective
  条件: [IsTorsionFree R M] {x : R} (hx : x != 0)
  证明: smul_right_injective _ hx

Depends on / 依赖: smul_right_injective
-/
theorem lsmul_injective [IsTorsionFree R M] {x : R} (hx : x != 0) :
    Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx

/--
theorem `ker_lsmul` / 定理 `ker_lsmul`

English:
theorem ker_lsmul
  given: [IsTorsionFree R M] {a : R} (ha : a != 0)
  proof: LinearMap.ker_eq_bot_of_injective (LinearMap.lsmul_injective ha)

中文:
定理 ker_lsmul
  条件: [IsTorsionFree R M] {a : R} (ha : a != 0)
  证明: LinearMap.ker_eq_bot_of_injective (LinearMap.lsmul_injective ha)

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot_of_injective, LinearMap.lsmul_injective, ker_eq_bot_of_injective, lsmul_injective
-/
theorem ker_lsmul [IsTorsionFree R M] {a : R} (ha : a != 0) :
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

variable (i : M' ->ₗ[S] M) (k : P' ->ₗ[S] P) (hk : Injective k)
  (f : M ->ₗ[R] P) (hf : forall m, f (i m) in LinearMap.range k)

/--
Definition of `restrictScalarsRange` / `restrictScalarsRange` 的定义

English:
definition restrictScalarsRange
  signature: :
  body: ((f.restrictScalars S).comp i).codLift k hk hf

中文:
定义 restrictScalarsRange
  签名: :
  定义体: ((f.restrictScalars S).comp i).codLift k hk hf

Depends on / 依赖: codLift, f.restrictScalars, restrictScalars
-/
noncomputable def restrictScalarsRange :
    M' ->ₗ[S] P' :=
  ((f.restrictScalars S).comp i).codLift k hk hf

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `restrictScalarsRange_apply` / 引理 `restrictScalarsRange_apply`

English:
lemma restrictScalarsRange_apply
  given: (m : M')
  proof: by
  have : k (restrictScalarsRange i k hk f hf m) =
      (k ∘ₗ ((f.restrictScalars S).comp i).codLift k hk hf) m :=
    rfl
  rw [this]; rw [comp_codLift]; rw [comp_apply]; rw [restrictScalars_apply]

@[simp]

中文:
引理 restrictScalarsRange_apply
  条件: (m : M')
  证明: by
  have : k (restrictScalarsRange i k hk f hf m) =
      (k ∘ₗ ((f.restrictScalars S).comp i).codLift k hk hf) m :=
    rfl
  rw [this]; rw [comp_codLift]; rw [comp_apply]; rw [restrictScalars_apply]

@[simp]

Depends on / 依赖: codLift, comp_apply, comp_codLift, f.restrictScalars, restrictScalars, restrictScalarsRange, restrictScalars_apply
-/
lemma restrictScalarsRange_apply (m : M') :
    k (restrictScalarsRange i k hk f hf m) = f (i m) := by
  have : k (restrictScalarsRange i k hk f hf m) =
      (k ∘ₗ ((f.restrictScalars S).comp i).codLift k hk hf) m :=
    rfl
  rw [this]; rw [comp_codLift]; rw [comp_apply]; rw [restrictScalars_apply]

@[simp]
/--
lemma `eq_restrictScalarsRange_iff` / 引理 `eq_restrictScalarsRange_iff`

English:
lemma eq_restrictScalarsRange_iff
  given: (m : M') (p : P')
  proof: by
  rw [← restrictScalarsRange_apply i k hk f hf m]; rw [hk.eq_iff]

@[simp]

中文:
引理 eq_restrictScalarsRange_iff
  条件: (m : M') (p : P')
  证明: by
  rw [← restrictScalarsRange_apply i k hk f hf m]; rw [hk.eq_iff]

@[simp]

Depends on / 依赖: eq_iff, hk.eq_iff, restrictScalarsRange_apply
-/
lemma eq_restrictScalarsRange_iff (m : M') (p : P') :
    p = restrictScalarsRange i k hk f hf m ↔ k p = f (i m) := by
  rw [← restrictScalarsRange_apply i k hk f hf m]; rw [hk.eq_iff]

@[simp]
/--
lemma `restrictScalarsRange_apply_eq_zero_iff` / 引理 `restrictScalarsRange_apply_eq_zero_iff`

English:
lemma restrictScalarsRange_apply_eq_zero_iff
  given: (m : M')
  proof: by
  rw [← hk.eq_iff]; rw [restrictScalarsRange_apply]; rw [map_zero]

中文:
引理 restrictScalarsRange_apply_eq_zero_iff
  条件: (m : M')
  证明: by
  rw [← hk.eq_iff]; rw [restrictScalarsRange_apply]; rw [map_zero]

Depends on / 依赖: eq_iff, hk.eq_iff, map_zero, restrictScalarsRange_apply
-/
lemma restrictScalarsRange_apply_eq_zero_iff (m : M') :
    restrictScalarsRange i k hk f hf m = 0 ↔ f (i m) = 0 := by
  rw [← hk.eq_iff]; rw [restrictScalarsRange_apply]; rw [map_zero]

end restrictScalarsRange

section restrictScalarsRange₂

variable {R S M N P M' N' P' : Type*}
  [CommSemiring R] [CommSemiring S] [SMul S R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
  [Module S M] [Module S N] [Module S P]
  [IsScalarTower S R M] [IsScalarTower S R N] [IsScalarTower S R P]
  [AddCommMonoid M'] [Module S M'] [AddCommMonoid N'] [Module S N'] [AddCommMonoid P'] [Module S P']
  [SMulCommClass R S P]

variable (i : M' ->ₗ[S] M) (j : N' ->ₗ[S] N) (k : P' ->ₗ[S] P) (hk : Injective k)
  (B : M ->ₗ[R] N ->ₗ[R] P) (hB : forall m n, B (i m) (j n) in LinearMap.range k)

/--
Definition of `restrictScalarsRange₂` / `restrictScalarsRange₂` 的定义

English:
definition restrictScalarsRange₂
  signature: :
  body: (((LinearMap.restrictScalarsₗ S R _ _ _).comp
    (B.restrictScalars S)).compl₁₂ i j).codRestrict₂ k hk hB

中文:
定义 restrictScalarsRange₂
  签名: :
  定义体: (((LinearMap.restrictScalarsₗ S R _ _ _).comp
    (B.restrictScalars S)).compl₁₂ i j).codRestrict₂ k hk hB

Depends on / 依赖: B.restrictScalars, LinearMap, LinearMap.restrictScalars, restrictScalars
-/
noncomputable def restrictScalarsRange₂ :
    M' ->ₗ[S] N' ->ₗ[S] P' :=
  (((LinearMap.restrictScalarsₗ S R _ _ _).comp
    (B.restrictScalars S)).compl₁₂ i j).codRestrict₂ k hk hB

set_option backward.isDefEq.respectTransparency false in
/--
lemma `restrictScalarsRange₂_apply` / 引理 `restrictScalarsRange₂_apply`

English:
lemma restrictScalarsRange₂_apply
  given: (m : M') (n : N')
  proof: by
  simp [restrictScalarsRange₂]

@[simp]

中文:
引理 restrictScalarsRange₂_apply
  条件: (m : M') (n : N')
  证明: by
  simp [restrictScalarsRange₂]

@[simp]
-/
@[simp] lemma restrictScalarsRange₂_apply (m : M') (n : N') :
    k (restrictScalarsRange₂ i j k hk B hB m n) = B (i m) (j n) := by
  simp [restrictScalarsRange₂]

@[simp]
/--
lemma `eq_restrictScalarsRange₂_iff` / 引理 `eq_restrictScalarsRange₂_iff`

English:
lemma eq_restrictScalarsRange₂_iff
  given: (m : M') (n : N') (p : P')
  proof: by
  rw [← restrictScalarsRange₂_apply i j k hk B hB m n]; rw [hk.eq_iff]

@[simp]

中文:
引理 eq_restrictScalarsRange₂_iff
  条件: (m : M') (n : N') (p : P')
  证明: by
  rw [← restrictScalarsRange₂_apply i j k hk B hB m n]; rw [hk.eq_iff]

@[simp]

Depends on / 依赖: eq_iff, hk.eq_iff
-/
lemma eq_restrictScalarsRange₂_iff (m : M') (n : N') (p : P') :
    p = restrictScalarsRange₂ i j k hk B hB m n ↔ k p = B (i m) (j n) := by
  rw [← restrictScalarsRange₂_apply i j k hk B hB m n]; rw [hk.eq_iff]

@[simp]
/--
lemma `restrictScalarsRange₂_apply_eq_zero_iff` / 引理 `restrictScalarsRange₂_apply_eq_zero_iff`

English:
lemma restrictScalarsRange₂_apply_eq_zero_iff
  given: (m : M') (n : N')
  proof: by
  rw [← hk.eq_iff]; rw [restrictScalarsRange₂_apply]; rw [map_zero]

中文:
引理 restrictScalarsRange₂_apply_eq_zero_iff
  条件: (m : M') (n : N')
  证明: by
  rw [← hk.eq_iff]; rw [restrictScalarsRange₂_apply]; rw [map_zero]

Depends on / 依赖: eq_iff, hk.eq_iff, map_zero
-/
lemma restrictScalarsRange₂_apply_eq_zero_iff (m : M') (n : N') :
    restrictScalarsRange₂ i j k hk B hB m n = 0 ↔ B (i m) (j n) = 0 := by
  rw [← hk.eq_iff]; rw [restrictScalarsRange₂_apply]; rw [map_zero]

end restrictScalarsRange₂

end LinearMap

section IsBilinearMap

variable
  (R : Type*) [CommSemiring R]
  {E : Type*} [AddCommMonoid E] [Module R E]
  {F : Type*} [AddCommMonoid F] [Module R F]
  {G : Type*} [AddCommMonoid G] [Module R G]

-- TODO Also make a semi-linear version.
/--
Definition of `IsBilinearMap` / `IsBilinearMap` 的定义

English:
structure IsBilinearMap
  parameters: (f : E -> F -> G)
  axioms and operations (4):
    - add_left : forall (x₁ x₂ : E) (y : F), f (x₁ + x₂) y = f x₁ y + f x₂ y
    - smul_left : forall (c : R) (x : E) (y : F), f (c • x) y = c • f x y
    - add_right : forall (x : E) (y₁ y₂ : F), f x (y₁ + y₂) = f x y₁ + f x y₂
    - smul_right : forall (c : R) (x : E) (y : F), f x (c • y) = c • f x y

中文:
结构 IsBilinearMap
  参数: (f : E -> F -> G)
  公理与运算 (4 个):
    - add_left : 对任意 (x₁ x₂ : E) (y : F), f (x₁ + x₂) y = f x₁ y + f x₂ y
    - smul_left : 对任意 (c : R) (x : E) (y : F), f (c • x) y = c • f x y
    - add_right : 对任意 (x : E) (y₁ y₂ : F), f x (y₁ + y₂) = f x y₁ + f x y₂
    - smul_right : 对任意 (c : R) (x : E) (y : F), f x (c • y) = c • f x y
-/
structure IsBilinearMap (f : E -> F -> G) : Prop where
  add_left : forall (x₁ x₂ : E) (y : F), f (x₁ + x₂) y = f x₁ y + f x₂ y
  smul_left : forall (c : R) (x : E) (y : F), f (c • x) y = c • f x y
  add_right : forall (x : E) (y₁ y₂ : F), f x (y₁ + y₂) = f x y₁ + f x y₂
  smul_right : forall (c : R) (x : E) (y : F), f x (c • y) = c • f x y

variable {R} in
/--
Definition of `IsBilinearMap.toLinearMap` / `IsBilinearMap.toLinearMap` 的定义

English:
definition IsBilinearMap.toLinearMap
  signature: {f : E -> F -> G} (hf : IsBilinearMap R f)
  body: LinearMap.mk₂ _ f hf.add_left hf.smul_left hf.add_right hf.smul_right

中文:
定义 IsBilinearMap.toLinearMap
  签名: {f : E -> F -> G} (hf : IsBilinearMap R f)
  定义体: LinearMap.mk₂ _ f hf.add_left hf.smul_left hf.add_right hf.smul_right

Depends on / 依赖: LinearMap, LinearMap.mk, add_left, add_right, hf.add_left, hf.add_right, hf.smul_left, hf.smul_right, smul_left, smul_right
-/
def IsBilinearMap.toLinearMap {f : E -> F -> G} (hf : IsBilinearMap R f) :
    E ->ₗ[R] F ->ₗ[R] G :=
  LinearMap.mk₂ _ f hf.add_left hf.smul_left hf.add_right hf.smul_right

end IsBilinearMap
