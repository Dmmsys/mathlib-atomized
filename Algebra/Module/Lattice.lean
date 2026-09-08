/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. Then an `R`-submodule `M` of `V` is a lattice,
if `M` is finitely generated and spans `V` as an `A`-module.

The typical use case is `A = K` is the fraction field of an integral domain `R` and `V = ι → K`
for some finite `ι`. The scalar multiple a lattice by a unit in `K` is again a lattice. This gives
rise to a homothety relation.

When `R` is a DVR and `ι = Fin 2`, then by taking the quotient of the type of `R`-lattices in
`ι → K` by the homothety relation, one obtains the vertices of what is called the Bruhat-Tits tree
of `GL 2 K`.

## Main definitions

- `Submodule.IsLattice`: An `R`-submodule `M` of `V` is a lattice, if it is finitely generated
  and its `A`-span is `V`.

## Main properties

Let `R` be a PID and `A = K` its field of fractions.

- `Submodule.IsLattice.free`: Every lattice in `V` is `R`-free.
- `Basis.extendOfIsLattice`: Any `R`-basis of a lattice `M` in `V` defines a `K`-basis of `V`.
- `Submodule.IsLattice.rank`: The `R`-rank of a lattice in `V` is equal to the `K`-rank of `V`.
- `Submodule.IsLattice.inf`: The intersection of two lattices is a lattice.

## Note

In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` where the finitely
generated condition is replaced by having the discrete topology. This is for example used
for complex tori.
-/

@[expose] public section

open Module
open scoped Pointwise

universe u

variable {R : Type*} [CommRing R]

namespace Submodule

/--
An `R`-submodule `M` of `V` is a lattice if it is finitely generated
and spans `V` as an `A`-module.

Note 1: `A` is marked as an `outParam` here. In practice this should not cause issues, since
`R` and `A` are fixed, where typically `A` is the fraction field of `R`.

Note 2: In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` where the finitely
generated condition is replaced by having the discrete topology. -/
/-
**Submodule.IsLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     (A : outParam (Type u_2)) →  
     [inst_1 : CommRing A] →         [inst_2 : Algebra R A] →           {V : Typ
e u_3} →             [inst_3 : AddCommMonoid V] →               [inst_4 : _root_
.Module R V] →                 [inst_5 : _root_.Module A V] → [IsScalarTower R A
 V] → [IsScalarTower R A V] → Submodule R V → Prop
参数：A : outParam (Type u_2)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-submodule `M` of `V` is a lattice if it is finitely generated
and spans `V` as an `A`-module.

Note 1: `A` is marked as an `outParam` here. In practice this should not cause i
ssues, since
`R` and `A` are fixed, where typically `A` is the fraction field of `R`.

Note 2: In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` wher
e the finitely
generated condition is replaced by having the discrete topology.
-/
class IsLattice (A : outParam Type*) [CommRing A] [Algebra R A]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]
    [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span A (M : Set V) = ⊤

namespace IsLattice

section

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable (M : Submodule R V)

/-- Any `R`-lattice is finite. -/
/-
**Submodule.IsLattice.finite** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsLattice`。
形式化陈述：finite [IsLattice A M] : Module.Finite R M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Submodule.IsLattice.fg`：∀ {R : Type u_1} {inst : CommRing R} {A : outPar
am (Type u_2)} {inst_1 : CommRing A} {inst_2 : Algebra R A}   {V : Type u_3} {in
st_3 : AddCo…

--- 原说明 ---
Any `R`-lattice is finite.
-/
instance finite [IsLattice A M] : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg

set_option backward.isDefEq.respectTransparency false in
/-- The action of `Aˣ` on `R`-submodules of `V` preserves `IsLattice`. -/
/-
**Submodule.IsLattice.smul** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsLattice`。
形式化陈述：smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where 
fg
参数：a : Aˣ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Submodule.IsLattice.fg`：∀ {R : Type u_1} {inst : CommRing R} {A : outPar
am (Type u_2)} {inst_1 : CommRing A} {inst_2 : Algebra R A}   {V : Type u_3} {in
st_3 : AddCo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smul_span`：smul_span (a : α) (s : Set M) : a • span R s = span
 R (a • s)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.fg_span`：fg_span {s : Set M} (hs : s.Finite) : FG (span R s)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Submodule.coe_pointwise_smul`：coe_pointwise_smul (a : α) (S : Submodule 
R M) : ↑(a • S) = a • (S : Set M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsLattice.span_eq_top`：∀ {R : Type u_1} {inst : CommRing R} {A
 : outParam (Type u_2)} {inst_1 : CommRing A} {inst_2 : Algebra R A}   {V : Type
 u_3} {inst_3 : AddCo…
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : M) (a : 
α) (S : Submodule R M) : m in S -> a • m in a • S

--- 原说明 ---
The action of `Aˣ` on `R`-submodules of `V` preserves `IsLattice`.
-/
instance smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where
  fg := by
    obtain ⟨s, rfl⟩ := IsLattice.fg (M := M)
    rw [Submodule.smul_span]
    have : Finite (a • (s : Set V) : Set V) := Finite.Set.finite_image _ _
    exact Submodule.fg_span (Set.toFinite (a • (s : Set V)))
  span_eq_top := by
    rw [Submodule.coe_pointwise_smul, ← Submodule.smul_span, IsLattice.span_eq_top]
    ext x
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    rw [show x = a • a⁻¹ • x by simp]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial)
/-
**Submodule.IsLattice.of_le_of_isLattice_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Submod
ule.IsLattice`。
形式化陈述：of_le_of_isLattice_of_fg {M N : Submodule R V} (hle : M <= N) [IsLattice A
 M] (hfg : N.FG) : IsLattice A N
参数：hle : M <= N；hfg : N.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsLattice.span_eq_top`：∀ {R : Type u_1} {inst : CommRing R} {A
 : outParam (Type u_2)} {inst_1 : CommRing A} {inst_2 : Algebra R A}   {V : Type
 u_3} {inst_3 : AddCo…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
-/
lemma of_le_of_isLattice_of_fg {M N : Submodule R V} (hle : M ≤ N) [IsLattice A M]
    (hfg : N.FG) : IsLattice A N :=
  ⟨hfg, eq_top_iff.mpr <|
    le_trans (by rw [IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

/-- The supremum of two lattices is a lattice. -/
/-
**Submodule.IsLattice.sup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsLattice`。
形式化陈述：sup (M N : Submodule R V) [IsLattice A M] [IsLattice A N] : IsLattice A (M
 ⊔ N)
参数：M N : Submodule R V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.IsLattice.of_le_of_isLattice_of_fg`：of_le_of_isLattice_of_fg {
M N : Submodule R V} (hle : M <= N) [IsLattice A M] (hfg : N.FG) : IsLattice A N
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `Submodule.IsLattice.fg`：∀ {R : Type u_1} {inst : CommRing R} {A : outPar
am (Type u_2)} {inst_1 : CommRing A} {inst_2 : Algebra R A}   {V : Type u_3} {in
st_3 : AddCo…

--- 原说明 ---
The supremum of two lattices is a lattice.
-/
instance sup (M N : Submodule R V) [IsLattice A M] [IsLattice A N] :
    IsLattice A (M ⊔ N) :=
  of_le_of_isLattice_of_fg A le_sup_left (Submodule.FG.sup IsLattice.fg IsLattice.fg)

end

section Field

variable {K : Type*} [Field K] [Algebra R K]

/-
**Submodule.IsLattice._root_.Submodule.span_range_eq_top_of_injective_of_rank_le
** 是 Mathlib 中的一个引理，位于命名空间 `Submodule.IsLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submodule.span_range_eq_top_of_injective_of_rank_le {M N : Type u} [IsDomain R]
    [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N] [Module.Finite K N]
    {f : M →ₗ[R] N} (hf : Function.Injective f) (h : Module.rank K N ≤ Module.rank R M) :
    Submodule.span K (LinearMap.range f : Set N) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h)
  rw [← Module.finrank_eq_rank, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ f x.val) ⊆ (LinearMap.range f : Set N) := by
    rintro x ⟨a, rfl⟩
    simp
  rw [eq_top_iff, ← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- Any basis of an `R`-lattice in `V` defines a `K`-basis of `V`. -/
/-
**Submodule.IsLattice._root_.Module.Basis.extendOfIsLattice** 是 Mathlib 中的一个定义，位
于命名空间 `Submodule.IsLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any basis of an `R`-lattice in `V` defines a `K`-basis of `V`.
-/
noncomputable def _root_.Module.Basis.extendOfIsLattice [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) :
    Basis κ K V :=
  have hli : LinearIndependent K (fun i ↦ (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearIndependent s g hs
  have hsp : ⊤ ≤ span K (Set.range fun i ↦ (M.subtype ∘ b) i) := by
    rw [← Submodule.span_span_of_tower R, Set.range_comp, ← Submodule.map_span]
    simp [b.span_eq, Submodule.map_top, span_eq_top]
  Basis.mk hli hsp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Submodule.IsLattice._root_.Module.Basis.extendOfIsLattice_apply** 是 Mathlib 中的
一个引理，位于命名空间 `Submodule.IsLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.Basis.extendOfIsLattice_apply [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) (k : κ) :
    b.extendOfIsLattice K k = (b k).val := by
  simp [Basis.extendOfIsLattice]

variable [IsDomain R]

/-- A finitely-generated `R`-submodule of `V` of rank at least the `K`-rank of `V`
is a lattice. -/
/-
**Submodule.IsLattice.of_rank_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule.IsLattice`
。
形式化陈述：of_rank_le [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V} (h
fg : M.FG) (hr : Module.rank K V <= Module.rank R M) : IsLattice K M where fg
参数：hfg : M.FG；hr : Module.rank K V <= Module.rank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.span_range_eq_top_of_injective_of_rank_le`：∀ {R : Type u_1} [i
nst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] {M N 
: Type u}   [IsDomain R] [IsFractionRing …
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype

--- 原说明 ---
A finitely-generated `R`-submodule of `V` of rank at least the `K`-rank of `V`
is a lattice.
-/
lemma of_rank_le [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
    (hfg : M.FG) (hr : Module.rank K V ≤ Module.rank R M) : IsLattice K M where
  fg := hfg
  span_eq_top := by
    simpa using Submodule.span_range_eq_top_of_injective_of_rank_le M.injective_subtype hr

variable [IsPrincipalIdealRing R]

/-- Any lattice over a PID is a free `R`-module.
Note that under our conditions, `Module.IsTorsionFree R K` simply says that `algebraMap R K` is
injective. -/
/-
**Submodule.IsLattice.free** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsLattice`。
形式化陈述：free [Module.IsTorsionFree R K] (M : Submodule R V) [IsLattice K M] : Modu
le.Free R M
参数：M : Submodule R V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.IsTorsionFree.trans_faithfulSMul`：Module.IsTorsionFree.trans_fait
hfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M] [Module A M] [Modu
le R M] [IsTorsionFree A M] […
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…

--- 原说明 ---
Any lattice over a PID is a free `R`-module.
Note that under our conditions, `Module.IsTorsionFree R K` simply says that `alg
ebraMap R K` is
injective.
-/
instance free [Module.IsTorsionFree R K] (M : Submodule R V) [IsLattice K M] : Module.Free R M := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  -- any torsion free finite module over a PID is free
  infer_instance

/-- Any lattice has `R`-rank equal to the `K`-rank of `V`. -/
/-
**Submodule.IsLattice.rank'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule.IsLattice`。
形式化陈述：rank' [IsFractionRing R K] (M : Submodule R V) [IsLattice K M] : Module.ra
nk R M = Module.rank K V
参数：M : Submodule R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R

--- 原说明 ---
Any lattice has `R`-rank equal to the `K`-rank of `V`.
-/
lemma rank' [IsFractionRing R K] (M : Submodule R V) [IsLattice K M] :
    Module.rank R M = Module.rank K V := by
  let b := Module.Free.chooseBasis R M
  rw [rank_eq_card_basis b, ← rank_eq_card_basis (b.extendOfIsLattice K)]

/-- Any `R`-lattice in `ι → K` has `#ι` as `R`-rank. -/
/-
**Submodule.IsLattice.rank_of_pi** 是 Mathlib 中的一个引理，位于命名空间 `Submodule.IsLattice`
。
形式化陈述：rank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (
ι -> K)) [IsLattice K M] : Module.rank R M = Fintype.card ι
参数：M : Submodule R (ι -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.IsLattice.rank'`：rank' [IsFractionRing R K] (M : Submodule R V
) [IsLattice K M] : Module.rank R M = Module.rank K V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_pi`：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.s
um fun i => Module.rank R (φ i)
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any `R`-lattice in `ι → K` has `#ι` as `R`-rank.
-/
lemma rank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι → K))
    [IsLattice K M] : Module.rank R M = Fintype.card ι := by
  rw [IsLattice.rank' K M]
  simp

/-- `Module.finrank` version of `IsLattice.rank`. -/
/-
**Submodule.IsLattice.finrank_of_pi** 是 Mathlib 中的一个引理，位于命名空间 `Submodule.IsLatti
ce`。
形式化陈述：finrank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule 
R (ι -> K)) [IsLattice K M] : Module.finrank R M = Fintype.card ι
参数：M : Submodule R (ι -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用引理 `Submodule.IsLattice.rank_of_pi`：rank_of_pi {ι : Type*} [Fintype ι] [IsFr
actionRing R K] (M : Submodule R (ι -> K)) [IsLattice K M] : Module.rank R M = F
intype.card ι

--- 原说明 ---
`Module.finrank` version of `IsLattice.rank`.
-/
lemma finrank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι → K))
    [IsLattice K M] : Module.finrank R M = Fintype.card ι :=
  Module.finrank_eq_of_rank_eq (IsLattice.rank_of_pi K M)

/-- The intersection of two lattices is a lattice. -/
/-
**Submodule.IsLattice.inf** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsLattice`。
形式化陈述：inf [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V) [IsLatt
ice K M] [IsLattice K N] : IsLattice K (M ⊓ N) where fg
参数：M N : Submodule R V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_le`：isNoetherian_of_le {s t : Submodule R M} [ht : IsNoe
therian R t] (h : s <= t) : IsNoetherian R s
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.span_range_eq_top_of_injective_of_rank_le`：∀ {R : Type u_1} [i
nst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra R K] {M N 
: Type u}   [IsDomain R] [IsFractionRing …
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.rank_sup_add_rank_inf_eq`：Submodule.rank_sup_add_rank_inf_eq (
s t : Submodule R M) : Module.rank R (s ⊔ t : Submodule R M) + Module.rank R (s 
⊓ t : Submodule R M) = M…
· 使用定理 `Cardinal.eq_of_add_eq_add_left`：∀ {a b c : Cardinal.{u_1}}, a + b = a + 
c → a < Cardinal.aleph0 → b = c
· 使用引理 `Submodule.IsLattice.rank'`：rank' [IsFractionRing R K] (M : Submodule R V
) [IsLattice K M] : Module.rank R M = Module.rank K V
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The intersection of two lattices is a lattice.
-/
instance inf [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V)
    [IsLattice K M] [IsLattice K N] : IsLattice K (M ⊓ N) where
  fg := by
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [← range_subtype (M ⊓ N)]
    apply Submodule.span_range_eq_top_of_injective_of_rank_le (M ⊓ N).injective_subtype
    have h := Submodule.rank_sup_add_rank_inf_eq M N
    rw [IsLattice.rank' K M, IsLattice.rank' K N, IsLattice.rank'] at h
    rw [Cardinal.eq_of_add_eq_add_left h (Module.rank_lt_aleph0 K V)]

end Field

end IsLattice

end Submodule

