/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Lie.Cochain

/-!
# Extensions of Lie algebras

This file defines extensions of Lie algebras, given by short exact sequences of Lie algebra
homomorphisms. They are implemented in two ways: `IsExtension` is a `Prop`-valued class taking two
homomorphisms as parameters, and `Extension` is a structure that includes the middle Lie algebra.

Because our sign convention for differentials is opposite that of Chevalley-Eilenberg, there is a
change of signs in the "action" part of the Lie bracket.

## Main definitions
* `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
* `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
* `LieAlgebra.IsExtension.extension`: A function that builds the bundled structure from the class.
* `LieAlgebra.ofTwoCocycle`: The Lie algebra built from a direct product, but whose bracket product
  is sheared by a 2-cocycle.
* `LieAlgebra.Extension.ofTwoCocycle`: The Lie algebra extension constructed from a 2-cocycle.
* `LieAlgebra.Extension.ringModuleOf`: Given an extension whose kernel is abelian, we obtain a Lie
  action of the target on the kernel.
* `LieAlgebra.Extension.twoCocycle`: The 2-cocycle attached to an extension with a linear section.
* `LieAlgebra.Extension.oneCochainOfTwoSplitting`: A 1-cochain attached to a pair of linear sections
  of an extension.

## TODO
* `IsCentral` - central extensions
* `Equiv` - equivalence of extensions

## References
* [Chevalley, Eilenberg, *Cohomology Theory of Lie Groups and Lie
  Algebras*](chevalley_eilenberg_1948)
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

@[expose] public section

open Function

namespace LieAlgebra

variable {R N L M : Type*}

section IsExtension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/--
Definition of `IsExtension` / `IsExtension` 的定义

English:
class IsExtension
  parameters: (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M)
  axioms and operations (3):
    - ker_eq_bot : i.ker = ⊥
    - range_eq_top : p.range = ⊤
    - exact : i.range = p.ker

中文:
类 是扩张
  参数: (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M)
  公理与运算 (3 个):
    - ker_eq_bot : i.ker = ⊥
    - range_eq_top : p.range = ⊤
    - exact : i.range = p.ker
-/
class IsExtension (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

/--
lemma `_root_.LieHom.range_eq_ker_iff` / 引理 `_root_.LieHom.range_eq_ker_iff`

English:
lemma _root_.LieHom.range_eq_ker_iff
  given: (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M)
  proof: ⟨fun h x => by simp [← LieHom.coe_range, h], fun h => (p.ker.toLieSubalgebra.ext i.range h).symm⟩

中文:
引理 _root_.Lie态射.range_eq_ker_iff
  条件: (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M)
  证明: ⟨fun h x => by simp [← LieHom.coe_range, h], fun h => (p.ker.toLieSubalgebra.ext i.range h).symm⟩

Depends on / 依赖: LieHom, LieHom.coe_range, coe_range, i.range, p.ker.toLieSubalgebra.ext, toLieSubalgebra
-/
lemma _root_.LieHom.range_eq_ker_iff (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M) :
    i.range = p.ker ↔ Exact i p :=
  ⟨fun h x => by simp [← LieHom.coe_range, h], fun h => (p.ker.toLieSubalgebra.ext i.range h).symm⟩

/--
Definition of `IsExtension.kerEquivRange` / `IsExtension.kerEquivRange` 的定义

English:
definition IsExtension.kerEquivRange
  signature: (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M) [IsExtension i p]
  body: .ofEq (R := R) (M := L) p.ker i.range by simp [exact (i := i) (p := p)]

中文:
定义 是扩张.kerEquivRange
  签名: (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M) [是扩张 i p]
  定义体: .ofEq (R := R) (M := L) p.ker i.range by simp [exact (i := i) (p := p)]

Depends on / 依赖: i.range, p.ker
-/
def IsExtension.kerEquivRange (i : N ->ₗ⁅R⁆ L) (p : L ->ₗ⁅R⁆ M) [IsExtension i p] :
    p.ker ≃ₗ[R] i.range :=
.ofEq (R := R) (M := L) p.ker i.range by simp [exact (i := i) (p := p)]

variable (R N M) in
/--
Definition of `Extension` / `Extension` 的定义

English:
structure Extension
  parameters: where
  axioms and operations (6):
    - L : Type*
    - instLieRing : LieRing L
    - instLieAlgebra : LieAlgebra R L
    - incl : N ->ₗ⁅R⁆ L
    - proj : L ->ₗ⁅R⁆ M
    - IsExtension : IsExtension incl proj

中文:
结构 扩张
  参数: where
  公理与运算 (6 个):
    - L : 类型
    - instLieRing : Lie环 L
    - instLieAlgebra : Lie代数 R L
    - incl : N ->ₗ⁅R⁆ L
    - proj : L ->ₗ⁅R⁆ M
    - IsExtension : 是扩张 incl proj
-/
structure Extension where
  /-- The middle object in the sequence. -/
  L : Type*
  /-- `L` is a Lie ring. -/
  instLieRing : LieRing L
  /-- `L` is a Lie algebra over `R`. -/
  instLieAlgebra : LieAlgebra R L
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  incl : N ->ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  proj : L ->ₗ⁅R⁆ M
  IsExtension : IsExtension incl proj

instance (E : Extension R M N) : LieRing E.L := E.instLieRing
instance (E : Extension R M N) : LieAlgebra R E.L := E.instLieAlgebra

/--
Definition of `IsExtension.extension` / `IsExtension.extension` 的定义

English:
definition IsExtension.extension
  signature: {i : N ->ₗ⁅R⁆ L} {p : L ->ₗ⁅R⁆ M} (h : IsExtension i p)
  body: ⟨L, _, _, i, p, h⟩

中文:
定义 是扩张.extension
  签名: {i : N ->ₗ⁅R⁆ L} {p : L ->ₗ⁅R⁆ M} (h : 是扩张 i p)
  定义体: ⟨L, _, _, i, p, h⟩
-/
@[simps] def IsExtension.extension {i : N ->ₗ⁅R⁆ L} {p : L ->ₗ⁅R⁆ M} (h : IsExtension i p) :
    Extension R N M :=
  ⟨L, _, _, i, p, h⟩

/--
lemma `isExtension_of_surjective` / 引理 `isExtension_of_surjective`

English:
lemma isExtension_of_surjective
  given: (f : L ->ₗ⁅R⁆ M) (hf : Surjective f)
  proof: LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

中文:
引理 isExtension_of_surjective
  条件: (f : L ->ₗ⁅R⁆ M) (hf : 满射 f)
  证明: LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

Depends on / 依赖: LieIdeal, LieIdeal.ker_incl, Module, Semiring, Semiring.toModule, f.ker, ker_incl, toModule
-/
lemma isExtension_of_surjective (f : L ->ₗ⁅R⁆ M) (hf : Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

end IsExtension

namespace Extension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/--
lemma `incl_apply_mem_ker` / 引理 `incl_apply_mem_ker`

English:
lemma incl_apply_mem_ker
  given: (E : Extension R M L) (x : M)
  proof: Exact.apply_apply_eq_zero ((E.incl.range_eq_ker_iff E.proj).mp E.IsExtension.exact) x

中文:
引理 incl_apply_mem_ker
  条件: (E : 扩张 R M L) (x : M)
  证明: Exact.apply_apply_eq_zero ((E.incl.range_eq_ker_iff E.proj).mp E.IsExtension.exact) x

Depends on / 依赖: E.IsExtension.exact, E.incl.range_eq_ker_iff, E.proj, Exact.apply_apply_eq_zero, IsExtension, apply_apply_eq_zero, range_eq_ker_iff
-/
lemma incl_apply_mem_ker (E : Extension R M L) (x : M) :
    E.incl x in E.proj.ker :=
  Exact.apply_apply_eq_zero ((E.incl.range_eq_ker_iff E.proj).mp E.IsExtension.exact) x

/--
lemma `proj_incl` / 引理 `proj_incl`

English:
lemma proj_incl
  given: (E : Extension R M L) (x : M)
  proof: LieHom.mem_ker.mp (incl_apply_mem_ker E x)

中文:
引理 proj_incl
  条件: (E : 扩张 R M L) (x : M)
  证明: LieHom.mem_ker.mp (incl_apply_mem_ker E x)
-/
@[simp] lemma proj_incl (E : Extension R M L) (x : M) :
    E.proj (E.incl x) = 0 :=
  LieHom.mem_ker.mp (incl_apply_mem_ker E x)

/--
lemma `incl_injective` / 引理 `incl_injective`

English:
lemma incl_injective
  given: (E : Extension R M L)
  proof: (LieHom.ker_eq_bot E.incl).mp E.IsExtension.ker_eq_bot

中文:
引理 incl_injective
  条件: (E : 扩张 R M L)
  证明: (LieHom.ker_eq_bot E.incl).mp E.IsExtension.ker_eq_bot

Depends on / 依赖: E.IsExtension.ker_eq_bot, E.incl, IsExtension, LieHom, LieHom.ker_eq_bot, ker_eq_bot
-/
lemma incl_injective (E : Extension R M L) :
    Injective E.incl :=
  (LieHom.ker_eq_bot E.incl).mp E.IsExtension.ker_eq_bot

/--
lemma `proj_surjective` / 引理 `proj_surjective`

English:
lemma proj_surjective
  given: (E : Extension R M L)
  proof: (LieHom.range_eq_top E.proj).mp E.IsExtension.range_eq_top

中文:
引理 proj_surjective
  条件: (E : 扩张 R M L)
  证明: (LieHom.range_eq_top E.proj).mp E.IsExtension.range_eq_top

Depends on / 依赖: E.IsExtension.range_eq_top, E.proj, IsExtension, LieHom, LieHom.range_eq_top, range_eq_top
-/
lemma proj_surjective (E : Extension R M L) :
    Surjective E.proj :=
  (LieHom.range_eq_top E.proj).mp E.IsExtension.range_eq_top

end Extension

section Algebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

open LieModule.Cohomology

/--
Definition of `ofTwoCocycle` / `ofTwoCocycle` 的定义

English:
structure ofTwoCocycle
  parameters: {R L M} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
  axioms and operations (1):
    - carrier : L × M

中文:
结构 ofTwoCocycle
  参数: {R L M} [交换环 R] [Lie环 L] [Lie代数 R L] [加法交换群 M]
  公理与运算 (1 个):
    - carrier : L × M
-/
structure ofTwoCocycle {R L M} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
    [Module R M] [LieRingModule L M] [LieModule R L M]
    (c : twoCocycle R L M) where
  /-- The underlying type. -/
  carrier : L × M

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (c : twoCocycle R L M)

/--
Definition of `ofProd` / `ofProd` 的定义

English:
definition ofProd
  signature: : L × M ≃ ofTwoCocycle c where
  body: ⟨a⟩
  invFun a := a.carrier

中文:
定义 ofProd
  签名: : L × M ≃ ofTwoCocycle c where
  定义体: ⟨a⟩
  invFun a := a.carrier
-/
def ofProd : L × M ≃ ofTwoCocycle c where
  toFun a := ⟨a⟩
  invFun a := a.carrier

-- transport instances along the equivalence
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (ofTwoCocycle c)
  body: (ofProd c).symm.addCommGroup

中文:
实例 :
  签名: 加法交换群 (ofTwoCocycle c)
  定义体: (ofProd c).symm.addCommGroup

Depends on / 依赖: addCommGroup, ofProd, symm.addCommGroup
-/
instance : AddCommGroup (ofTwoCocycle c) := (ofProd c).symm.addCommGroup
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (ofTwoCocycle c)
  body: (ofProd c).symm.module R

中文:
实例 :
  签名: 模 R (ofTwoCocycle c)
  定义体: (ofProd c).symm.module R

Depends on / 依赖: module, ofProd, symm.module
-/
instance : Module R (ofTwoCocycle c) := (ofProd c).symm.module R

/--
lemma `of_zero` / 引理 `of_zero`

English:
lemma of_zero
  statement: ofProd c (0 : L × M) = 0
  proof: rfl

中文:
引理 of_zero
  结论: ofProd c (0 : L × M) = 0
  证明: rfl

Depends on / 依赖: Finite, FinitePresentation, Module, Module.Finite, Module.FinitePresentation
-/
@[simp] lemma of_zero : ofProd c (0 : L × M) = 0 := rfl
/--
lemma `of_add` / 引理 `of_add`

English:
lemma of_add
  given: (x y : L × M)
  statement: ofProd c (x + y) = ofProd c x + ofProd c y
  proof: rfl

中文:
引理 of_add
  条件: (x y : L × M)
  结论: ofProd c (x + y) = ofProd c x + ofProd c y
  证明: rfl
-/
@[simp] lemma of_add (x y : L × M) : ofProd c (x + y) = ofProd c x + ofProd c y := rfl
/--
lemma `of_smul` / 引理 `of_smul`

English:
lemma of_smul
  given: (r : R) (x : L × M)
  statement: (ofProd c) (r • x) = r • ofProd c x
  proof: rfl

中文:
引理 of_smul
  条件: (r : R) (x : L × M)
  结论: (ofProd c) (r • x) = r • ofProd c x
  证明: rfl
-/
@[simp] lemma of_smul (r : R) (x : L × M) : (ofProd c) (r • x) = r • ofProd c x := rfl

/--
lemma `of_symm_zero` / 引理 `of_symm_zero`

English:
lemma of_symm_zero
  statement: (ofProd c).symm (0 : ofTwoCocycle c) = 0
  proof: rfl

中文:
引理 of_symm_zero
  结论: (ofProd c).symm (0 : ofTwoCocycle c) = 0
  证明: rfl
-/
@[simp] lemma of_symm_zero : (ofProd c).symm (0 : ofTwoCocycle c) = 0 := rfl
/--
lemma `of_symm_add` / 引理 `of_symm_add`

English:
lemma of_symm_add
  given: (x y : ofTwoCocycle c)
  proof: rfl

中文:
引理 of_symm_add
  条件: (x y : ofTwoCocycle c)
  证明: rfl
-/
@[simp] lemma of_symm_add (x y : ofTwoCocycle c) :
    (ofProd c).symm (x + y) = (ofProd c).symm x + (ofProd c).symm y := rfl
/--
lemma `of_symm_smul` / 引理 `of_symm_smul`

English:
lemma of_symm_smul
  given: (r : R) (x : ofTwoCocycle c)
  proof: rfl

中文:
引理 of_symm_smul
  条件: (r : R) (x : ofTwoCocycle c)
  证明: rfl
-/
@[simp] lemma of_symm_smul (r : R) (x : ofTwoCocycle c) :
    (ofProd c).symm (r • x) = r • (ofProd c).symm x := rfl

/--
lemma `of_nsmul` / 引理 `of_nsmul`

English:
lemma of_nsmul
  given: (n : Nat) (x : L × M)
  statement: (ofProd c) (n • x) = n • (ofProd c) x
  proof: rfl

中文:
引理 of_nsmul
  条件: (n : 自然数) (x : L × M)
  结论: (ofProd c) (n • x) = n • (ofProd c) x
  证明: rfl
-/
@[simp] lemma of_nsmul (n : Nat) (x : L × M) : (ofProd c) (n • x) = n • (ofProd c) x := rfl
/--
lemma `of_symm_nsmul` / 引理 `of_symm_nsmul`

English:
lemma of_symm_nsmul
  given: (n : Nat) (x : ofTwoCocycle c)
  proof: rfl

中文:
引理 of_symm_nsmul
  条件: (n : 自然数) (x : ofTwoCocycle c)
  证明: rfl
-/
@[simp] lemma of_symm_nsmul (n : Nat) (x : ofTwoCocycle c) :
    (ofProd c).symm (n • x) = n • (ofProd c).symm x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (ofTwoCocycle c)
  body: letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ofProd c (⁅x₁, y₁⁆, (c : L ->ₗ[R] L ->ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆)
  add_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [of_symm_add, Prod.fst_add, add_lie, twoCochain_val_apply, map_add,
      LinearMap.add_apply, Prod.snd_add, lie_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  lie_self x := by
    rw [← of_zero]; rw [c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [twoCochain_val_apply, Equiv.symm_apply_apply, lie_lie, Prod.mk_add_mk,
      sub_add_cancel, Prod.mk.injEq, true_and, lie_add, lie_sub]
    have hc := c.2
    rw [mem_twoCocycle_iff] at hc
    have := d₂₃_apply R L M c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1]; rw [((ofProd c).symm z).1⁆]; rw [← twoCochain_skew _ _ ⁅((ofProd c).symm y).1]; rw [((ofProd c).symm z).1⁆]; rw [eq_sub_iff_add_eq]; rw [zero_add]; rw [neg_eq_iff_eq_neg] at this
    rw [this]
    abel

中文:
实例 :
  签名: Lie环 (ofTwoCocycle c)
  定义体: letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ofProd c (⁅x₁, y₁⁆, (c : L ->ₗ[R] L ->ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆)
  add_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [of_symm_add, Prod.fst_add, add_lie, twoCochain_val_apply, map_add,
      LinearMap.add_apply, Prod.snd_add, lie_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  lie_self x := by
    rw [← of_zero]; rw [c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [twoCochain_val_apply, Equiv.symm_apply_apply, lie_lie, Prod.mk_add_mk,
      sub_add_cancel, Prod.mk.injEq, true_and, lie_add, lie_sub]
    have hc := c.2
    rw [mem_twoCocycle_iff] at hc
    have := d₂₃_apply R L M c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1]; rw [((ofProd c).symm z).1⁆]; rw [← twoCochain_skew _ _ ⁅((ofProd c).symm y).1]; rw [((ofProd c).symm z).1⁆]; rw [eq_sub_iff_add_eq]; rw [zero_add]; rw [neg_eq_iff_eq_neg] at this
    rw [this]
    abel

Depends on / 依赖: Equiv.congr_arg, LinearMap, LinearMap.add_apply, Prod.fst_add, Prod.mk.injEq, Prod.mk_add_mk, Prod.snd_add, add_apply, add_lie, congr_arg, fst_add, lie_add, map_add, mk_add_mk, ofProd, of_add, of_symm_add, snd_add, true_and, twoCochain_val_apply
-/
instance : LieRing (ofTwoCocycle c) where
  bracket x y :=
    letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ofProd c (⁅x₁, y₁⁆, (c : L ->ₗ[R] L ->ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆)
  add_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [of_symm_add, Prod.fst_add, add_lie, twoCochain_val_apply, map_add,
      LinearMap.add_apply, Prod.snd_add, lie_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  lie_add x y z := by
    rw [← of_add]
    exact Equiv.congr_arg (by simp; abel)
  lie_self x := by
    rw [← of_zero]; rw [c.1.2]
    exact Equiv.congr_arg (by simp)
  leibniz_lie x y z := by
    rw [← of_add]
    refine Equiv.congr_arg ?_
    simp only [twoCochain_val_apply, Equiv.symm_apply_apply, lie_lie, Prod.mk_add_mk,
      sub_add_cancel, Prod.mk.injEq, true_and, lie_add, lie_sub]
    have hc := c.2
    rw [mem_twoCocycle_iff] at hc
    have := d₂₃_apply R L M c ((ofProd c).symm x).1 ((ofProd c).symm y).1 ((ofProd c).symm z).1
    simp only [hc, LinearMap.zero_apply] at this
    rw [← twoCochain_skew _ _ ⁅((ofProd c).symm x).1]; rw [((ofProd c).symm z).1⁆]; rw [← twoCochain_skew _ _ ⁅((ofProd c).symm y).1]; rw [((ofProd c).symm z).1⁆]; rw [eq_sub_iff_add_eq]; rw [zero_add]; rw [neg_eq_iff_eq_neg] at this
    rw [this]
    abel

/--
lemma `bracket_ofTwoCocycle` / 引理 `bracket_ofTwoCocycle`

English:
lemma bracket_ofTwoCocycle
  given: {c : twoCocycle R L M} (x y : ofTwoCocycle c)
  proof: ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ⁅x, y⁆ = ofProd c (⁅x₁, y₁⁆, (c : L ->ₗ[R] L ->ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆) :=
  rfl

中文:
引理 bracket_ofTwoCocycle
  条件: {c : twoCocycle R L M} (x y : ofTwoCocycle c)
  证明: ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ⁅x, y⁆ = ofProd c (⁅x₁, y₁⁆, (c : L ->ₗ[R] L ->ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆) :=
  rfl

Depends on / 依赖: ofProd
-/
lemma bracket_ofTwoCocycle {c : twoCocycle R L M} (x y : ofTwoCocycle c) :
    letI x₁ := ((ofProd c).symm x).1; letI x₂ := ((ofProd c).symm x).2
    letI y₁ := ((ofProd c).symm y).1; letI y₂ := ((ofProd c).symm y).2
    ⁅x, y⁆ = ofProd c (⁅x₁, y₁⁆, (c : L ->ₗ[R] L ->ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra R (ofTwoCocycle c)
  body: by
    simp only [bracket_ofTwoCocycle]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

中文:
实例 :
  签名: Lie代数 R (ofTwoCocycle c)
  定义体: by
    simp only [bracket_ofTwoCocycle]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

Depends on / 依赖: Equiv.congr_arg, bracket_ofTwoCocycle, congr_arg, smul_add, smul_sub
-/
instance : LieAlgebra R (ofTwoCocycle c) where
  lie_smul r x y := by
    simp only [bracket_ofTwoCocycle]
    exact Equiv.congr_arg (by simp [← smul_add, smul_sub])

/-- An equivalence of extended Lie algebras induced by translation by a coboundary. -/
@[simps]
/--
Definition of `LieEquiv.ofCoboundary` / `LieEquiv.ofCoboundary` 的定义

English:
definition LieEquiv.ofCoboundary
  signature: (c' : twoCocycle R L M) (x : oneCochain R L M)
  body: letI z := (ofProd c).symm y
    ofProd c' (z.1, z.2 - x z.1)
  invFun z :=
    letI y := (ofProd c').symm z
    ofProd c (y.1, y.2 + x y.1)
  map_add' _ _ := by simp [← of_add]; abel
  map_smul' := by simp [← of_smul, smul_sub]
map_lie' := ((ofProd c').eq_symm_apply).1 by simp [bracket_ofTwoCocycle, h]; abel
  left_inv y := by simp
  right_inv z := by simp

中文:
定义 Lie等价.ofCoboundary
  签名: (c' : twoCocycle R L M) (x : oneCochain R L M)
  定义体: letI z := (ofProd c).symm y
    ofProd c' (z.1, z.2 - x z.1)
  invFun z :=
    letI y := (ofProd c').symm z
    ofProd c (y.1, y.2 + x y.1)
  map_add' _ _ := by simp [← of_add]; abel
  map_smul' := by simp [← of_smul, smul_sub]
map_lie' := ((ofProd c').eq_symm_apply).1 by simp [bracket_ofTwoCocycle, h]; abel
  left_inv y := by simp
  right_inv z := by simp

Depends on / 依赖: bracket_ofTwoCocycle, eq_symm_apply, invFun, left_inv, map_add, map_lie, map_smul, ofProd, of_add, of_smul, right_inv, smul_sub
-/
def LieEquiv.ofCoboundary (c' : twoCocycle R L M) (x : oneCochain R L M)
    (h : c' = c + d₁₂ R L M x) :
    ofTwoCocycle c ≃ₗ⁅R⁆ ofTwoCocycle c' where
  toFun y :=
    letI z := (ofProd c).symm y
    ofProd c' (z.1, z.2 - x z.1)
  invFun z :=
    letI y := (ofProd c').symm z
    ofProd c (y.1, y.2 + x y.1)
  map_add' _ _ := by simp [← of_add]; abel
  map_smul' := by simp [← of_smul, smul_sub]
map_lie' := ((ofProd c').eq_symm_apply).1 by simp [bracket_ofTwoCocycle, h]; abel
  left_inv y := by simp
  right_inv z := by simp

end Algebra

namespace Extension

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

section TwoCocycle

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

/--
Definition of `ofTwoCocycle` / `ofTwoCocycle` 的定义

English:
definition ofTwoCocycle
  signature: : Extension R M L where
  body: LieAlgebra.ofTwoCocycle c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [trivial_lie_zero, bracket_ofTwoCocycle] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  IsExtension :=
    { ker_eq_bot := by
        rw [LieHom.ker_eq_bot]
        intro x y
        simp
      range_eq_top := by
        rw [LieHom.range_eq_top]
        intro x
        use (ofProd c (x, 0))
        simp
      exact := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, h⟩ := hx
          rw [← h]
          rfl
        · intro hx
          have : ((ofProd c).symm x).1 = 0 := hx
          simp only [LieHom.mem_range, LieHom.coe_mk]
          use ((ofProd c).symm x).2
          nth_rw 2 [← Equiv.apply_symm_apply (ofProd c) x]
          rw [← this] }

中文:
定义 ofTwoCocycle
  签名: : 扩张 R M L where
  定义体: LieAlgebra.ofTwoCocycle c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [trivial_lie_zero, bracket_ofTwoCocycle] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  IsExtension :=
    { ker_eq_bot := by
        rw [LieHom.ker_eq_bot]
        intro x y
        simp
      range_eq_top := by
        rw [LieHom.range_eq_top]
        intro x
        use (ofProd c (x, 0))
        simp
      exact := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, h⟩ := hx
          rw [← h]
          rfl
        · intro hx
          have : ((ofProd c).symm x).1 = 0 := hx
          simp only [LieHom.mem_range, LieHom.coe_mk]
          use ((ofProd c).symm x).2
          nth_rw 2 [← Equiv.apply_symm_apply (ofProd c) x]
          rw [← this] }

Depends on / 依赖: LieAlgebra, LieAlgebra.ofTwoCocycle, ofTwoCocycle
-/
def ofTwoCocycle : Extension R M L where
  L := LieAlgebra.ofTwoCocycle c
  instLieRing := inferInstance
  instLieAlgebra := inferInstance
  incl :=
    { toFun x := ofProd c (0, x)
      map_add' _ _ := by simp [← of_add]
      map_smul' _ _ := by simp [← of_smul]
      map_lie' {_ _} := by simp [trivial_lie_zero, bracket_ofTwoCocycle] }
  proj :=
    { toFun x := ((ofProd c).symm x).1
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_lie' {_ _} := by simp [bracket_ofTwoCocycle] }
  IsExtension :=
    { ker_eq_bot := by
        rw [LieHom.ker_eq_bot]
        intro x y
        simp
      range_eq_top := by
        rw [LieHom.range_eq_top]
        intro x
        use (ofProd c (x, 0))
        simp
      exact := by
        ext x
        constructor
        · intro hx
          obtain ⟨n, h⟩ := hx
          rw [← h]
          rfl
        · intro hx
          have : ((ofProd c).symm x).1 = 0 := hx
          simp only [LieHom.mem_range, LieHom.coe_mk]
          use ((ofProd c).symm x).2
          nth_rw 2 [← Equiv.apply_symm_apply (ofProd c) x]
          rw [← this] }

/--
Definition of `ofAlg` / `ofAlg` 的定义

English:
definition ofAlg
  signature: : LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L
  body: LieEquiv.refl

中文:
定义 ofAlg
  签名: : Lie代数.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L
  定义体: LieEquiv.refl

Depends on / 依赖: LieEquiv, LieEquiv.refl
-/
def ofAlg : LieAlgebra.ofTwoCocycle c ≃ₗ⁅R⁆ (ofTwoCocycle c).L := LieEquiv.refl

/--
lemma `bracket` / 引理 `bracket`

English:
lemma bracket
  given: (x y : (ofTwoCocycle c).L)
  proof: rfl

@[simp]

中文:
引理 bracket
  条件: (x y : (ofTwoCocycle c).L)
  证明: rfl

@[simp]
-/
lemma bracket (x y : (ofTwoCocycle c).L) :
    ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (ofAlg c).symm y⁆ :=
  rfl

@[simp]
/--
lemma `ofTwoCocycle_incl_apply` / 引理 `ofTwoCocycle_incl_apply`

English:
lemma ofTwoCocycle_incl_apply
  given: (x : M)
  statement: (ofTwoCocycle c).incl x = ⟨(0, x)⟩
  proof: rfl

@[simp]

中文:
引理 ofTwoCocycle_incl_apply
  条件: (x : M)
  结论: (ofTwoCocycle c).incl x = ⟨(0, x)⟩
  证明: rfl

@[simp]
-/
lemma ofTwoCocycle_incl_apply (x : M) : (ofTwoCocycle c).incl x = ⟨(0, x)⟩ :=
  rfl

@[simp]
/--
lemma `ofTwoCocycle_proj_apply` / 引理 `ofTwoCocycle_proj_apply`

English:
lemma ofTwoCocycle_proj_apply
  given: (x : (ofTwoCocycle c).L)
  statement: (ofTwoCocycle c).proj x = x.carrier.1
  proof: rfl

中文:
引理 ofTwoCocycle_proj_apply
  条件: (x : (ofTwoCocycle c).L)
  结论: (ofTwoCocycle c).proj x = x.carrier.1
  证明: rfl
-/
lemma ofTwoCocycle_proj_apply (x : (ofTwoCocycle c).L) : (ofTwoCocycle c).proj x = x.carrier.1 :=
  rfl

end TwoCocycle

/--
lemma `lie_incl_mem_ker` / 引理 `lie_incl_mem_ker`

English:
lemma lie_incl_mem_ker
  given: {E : Extension R M L} (x : E.L) (y : M)
  proof: by
  rw [LieHom.mem_ker]; rw [LieHom.map_lie]; rw [proj_incl]; rw [lie_zero]

中文:
引理 lie_incl_mem_ker
  条件: {E : 扩张 R M L} (x : E.L) (y : M)
  证明: by
  rw [LieHom.mem_ker]; rw [LieHom.map_lie]; rw [proj_incl]; rw [lie_zero]

Depends on / 依赖: LieHom, LieHom.map_lie, LieHom.mem_ker, lie_zero, map_lie, mem_ker, proj_incl
-/
lemma lie_incl_mem_ker {E : Extension R M L} (x : E.L) (y : M) :
    ⁅x, E.incl y⁆ in E.proj.ker := by
  rw [LieHom.mem_ker]; rw [LieHom.map_lie]; rw [proj_incl]; rw [lie_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toKer` / `toKer` 的定义

English:
definition toKer
  signature: (E : Extension R M L)
  body: ⟨E.incl m, E.incl_apply_mem_ker m⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {x y} := by ext; simp [← LieHom.map_lie]
  invFun := (Equiv.ofInjective E.incl E.incl_injective).symm ∘ E.IsExtension.kerEquivRange
  left_inv _ := by
    simp [IsExtension.kerEquivRange, Equiv.symm_apply_eq]
    rfl
  right_inv x := by simpa [Subtype.ext_iff] using! Equiv.apply_ofInjective_symm E.incl_injective _

中文:
定义 toKer
  签名: (E : 扩张 R M L)
  定义体: ⟨E.incl m, E.incl_apply_mem_ker m⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {x y} := by ext; simp [← LieHom.map_lie]
  invFun := (Equiv.ofInjective E.incl E.incl_injective).symm ∘ E.IsExtension.kerEquivRange
  left_inv _ := by
    simp [IsExtension.kerEquivRange, Equiv.symm_apply_eq]
    rfl
  right_inv x := by simpa [Subtype.ext_iff] using! Equiv.apply_ofInjective_symm E.incl_injective _

Depends on / 依赖: E.incl, E.incl_apply_mem_ker, incl_apply_mem_ker
-/
noncomputable def toKer (E : Extension R M L) :
    M ≃ₗ⁅R⁆ E.proj.ker where
  toFun m := ⟨E.incl m, E.incl_apply_mem_ker m⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' {x y} := by ext; simp [← LieHom.map_lie]
  invFun := (Equiv.ofInjective E.incl E.incl_injective).symm ∘ E.IsExtension.kerEquivRange
  left_inv _ := by
    simp [IsExtension.kerEquivRange, Equiv.symm_apply_eq]
    rfl
  right_inv x := by simpa [Subtype.ext_iff] using! Equiv.apply_ofInjective_symm E.incl_injective _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `lie_toKer_apply` / 引理 `lie_toKer_apply`

English:
lemma lie_toKer_apply
  given: (E : Extension R M L) (x : M) (y : E.L)
  proof: by
  rfl

中文:
引理 lie_toKer_apply
  条件: (E : 扩张 R M L) (x : M) (y : E.L)
  证明: by
  rfl

Depends on / 依赖: Subsingleton, of_subsingleton
-/
@[simp] lemma lie_toKer_apply (E : Extension R M L) (x : M) (y : E.L) :
    ⁅y, (E.toKer x : E.L)⁆ = ⁅y, E.incl x⁆ := by
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLieAbelian
  signature: M] (E
  body: (lie_abelian_iff_equiv_lie_abelian E.toKer.symm).mpr inferInstance

中文:
实例 [IsLieAbelian
  签名: M] (E
  定义体: (lie_abelian_iff_equiv_lie_abelian E.toKer.symm).mpr inferInstance

Depends on / 依赖: E.toKer.symm, lie_abelian_iff_equiv_lie_abelian
-/
instance [IsLieAbelian M] (E : Extension R M L) : IsLieAbelian E.proj.ker :=
  (lie_abelian_iff_equiv_lie_abelian E.toKer.symm).mpr inferInstance

/-- Given an extension of `L` by `M` whose kernel `M` is abelian, the kernel `M` gets an `L`-module
structure. We do not make this an instance, because we may have to work with more than one
extension. -/
@[simps, instance_reducible]
/--
Definition of `ringModuleOf` / `ringModuleOf` 的定义

English:
definition ringModuleOf
  signature: [IsLieAbelian M] (E : Extension R M L)
  body: E.toKer.symm ⁅E.proj_surjective.hasRightInverse.choose x, E.toKer y⁆
  add_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    rw [← map_add]; rw [← add_lie]; rw [eq_comm]; rw [EquivLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]
    exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
  lie_add x m n := by simp [← map_add, ← lie_add]
  leibniz_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    have aux (z : E.proj.ker) : ⁅⁅h.choose x, h.choose y⁆, z⁆ = ⁅h.choose ⁅x, y⁆, z⁆ := by
      rw [← sub_eq_zero]; rw [← sub_lie]
      exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ z
    rw [← map_add]; rw [EquivLike.apply_eq_iff_eq]; rw [LieEquiv.apply_symm_apply]; rw [LieEquiv.apply_symm_apply]; rw [leibniz_lie]; rw [aux]

中文:
定义 ringModuleOf
  签名: [IsLieAbelian M] (E : 扩张 R M L)
  定义体: E.toKer.symm ⁅E.proj_surjective.hasRightInverse.choose x, E.toKer y⁆
  add_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    rw [← map_add]; rw [← add_lie]; rw [eq_comm]; rw [EquivLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]
    exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
  lie_add x m n := by simp [← map_add, ← lie_add]
  leibniz_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    have aux (z : E.proj.ker) : ⁅⁅h.choose x, h.choose y⁆, z⁆ = ⁅h.choose ⁅x, y⁆, z⁆ := by
      rw [← sub_eq_zero]; rw [← sub_lie]
      exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ z
    rw [← map_add]; rw [EquivLike.apply_eq_iff_eq]; rw [LieEquiv.apply_symm_apply]; rw [LieEquiv.apply_symm_apply]; rw [leibniz_lie]; rw [aux]

Depends on / 依赖: E.proj_surjective.hasRightInverse.choose, E.toKer, E.toKer.symm, hasRightInverse, proj_surjective
-/
noncomputable def ringModuleOf [IsLieAbelian M] (E : Extension R M L) : LieRingModule L M where
  bracket x y := E.toKer.symm ⁅E.proj_surjective.hasRightInverse.choose x, E.toKer y⁆
  add_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    rw [← map_add]; rw [← add_lie]; rw [eq_comm]; rw [EquivLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]
    exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
  lie_add x m n := by simp [← map_add, ← lie_add]
  leibniz_lie x y m := by
    set h := E.proj_surjective.hasRightInverse
    have aux (z : E.proj.ker) : ⁅⁅h.choose x, h.choose y⁆, z⁆ = ⁅h.choose ⁅x, y⁆, z⁆ := by
      rw [← sub_eq_zero]; rw [← sub_lie]
      exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ z
    rw [← map_add]; rw [EquivLike.apply_eq_iff_eq]; rw [LieEquiv.apply_symm_apply]; rw [LieEquiv.apply_symm_apply]; rw [leibniz_lie]; rw [aux]

/--
lemma `ringModuleOf_bracket_proj` / 引理 `ringModuleOf_bracket_proj`

English:
lemma ringModuleOf_bracket_proj
  given: [IsLieAbelian M] (E : Extension R M L) (y : M) (z : E.L)
  proof: E.ringModuleOf
    ⁅E.proj z, y⁆ = E.toKer.symm ⁅z, E.toKer y⁆ := by
  obtain ⟨x, hx⟩ : E.proj_surjective.hasRightInverse.choose (E.proj z) - z in E.incl.range := by
    rw [E.IsExtension.exact]
    change _ in E.proj.ker
    simp [E.proj_surjective.hasRightInverse.choose_spec (E.proj z)]
  rw [ringModuleOf_bracket]; rw [EmbeddingLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]; rw [Subtype.ext_iff]; rw [LieSubmodule.coe_bracket]; rw [lie_toKer_apply]; rw [ZeroMemClass.coe_zero]; rw [← hx]; rw [LieHom.coe_toLinearMap]; rw [← LieHom.map_lie]; rw [trivial_lie_zero M M x y]; rw [map_zero]

中文:
引理 ringModuleOf_bracket_proj
  条件: [IsLieAbelian M] (E : 扩张 R M L) (y : M) (z : E.L)
  证明: E.ringModuleOf
    ⁅E.proj z, y⁆ = E.toKer.symm ⁅z, E.toKer y⁆ := by
  obtain ⟨x, hx⟩ : E.proj_surjective.hasRightInverse.choose (E.proj z) - z in E.incl.range := by
    rw [E.IsExtension.exact]
    change _ in E.proj.ker
    simp [E.proj_surjective.hasRightInverse.choose_spec (E.proj z)]
  rw [ringModuleOf_bracket]; rw [EmbeddingLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]; rw [Subtype.ext_iff]; rw [LieSubmodule.coe_bracket]; rw [lie_toKer_apply]; rw [ZeroMemClass.coe_zero]; rw [← hx]; rw [LieHom.coe_toLinearMap]; rw [← LieHom.map_lie]; rw [trivial_lie_zero M M x y]; rw [map_zero]

Depends on / 依赖: E.ringModuleOf, ringModuleOf
-/
lemma ringModuleOf_bracket_proj [IsLieAbelian M] (E : Extension R M L) (y : M) (z : E.L) :
    letI := E.ringModuleOf
    ⁅E.proj z, y⁆ = E.toKer.symm ⁅z, E.toKer y⁆ := by
  obtain ⟨x, hx⟩ : E.proj_surjective.hasRightInverse.choose (E.proj z) - z in E.incl.range := by
    rw [E.IsExtension.exact]
    change _ in E.proj.ker
    simp [E.proj_surjective.hasRightInverse.choose_spec (E.proj z)]
  rw [ringModuleOf_bracket]; rw [EmbeddingLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]; rw [Subtype.ext_iff]; rw [LieSubmodule.coe_bracket]; rw [lie_toKer_apply]; rw [ZeroMemClass.coe_zero]; rw [← hx]; rw [LieHom.coe_toLinearMap]; rw [← LieHom.map_lie]; rw [trivial_lie_zero M M x y]; rw [map_zero]

/--
lemma `lieModuleOf` / 引理 `lieModuleOf`

English:
lemma lieModuleOf
  given: [IsLieAbelian M] (E : Extension R M L)
  proof: E.ringModuleOf
    LieModule R L M := by
  let := E.ringModuleOf
  set h := E.proj_surjective.hasRightInverse
  exact
    { smul_lie r x m := by
        rw [ringModuleOf_bracket]; rw [ringModuleOf_bracket]; rw [← map_smul]; rw [← smul_lie]; rw [EquivLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]
        exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
      lie_smul r x m := by simp }

中文:
引理 lieModuleOf
  条件: [IsLieAbelian M] (E : 扩张 R M L)
  证明: E.ringModuleOf
    LieModule R L M := by
  let := E.ringModuleOf
  set h := E.proj_surjective.hasRightInverse
  exact
    { smul_lie r x m := by
        rw [ringModuleOf_bracket]; rw [ringModuleOf_bracket]; rw [← map_smul]; rw [← smul_lie]; rw [EquivLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]
        exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
      lie_smul r x m := by simp }

Depends on / 依赖: E.ringModuleOf, Finite, FinitePresentation, Function, Function.Exact, LinearMap, LinearMap.exact_iff, LinearMap.ker, LinearMap.lTensor_surjective, Module, Module.Finite, Module.Finite.exists_fin, Module.FinitePresentation.fg_ker, Module.finitePresentation_of_projective, Module.finitePresentation_of_surjective, baseChange, exact_iff, exact_subtype_ker_map, exists_fin, f.baseChange
-/
lemma lieModuleOf [IsLieAbelian M] (E : Extension R M L) :
    letI := E.ringModuleOf
    LieModule R L M := by
  let := E.ringModuleOf
  set h := E.proj_surjective.hasRightInverse
  exact
    { smul_lie r x m := by
        rw [ringModuleOf_bracket]; rw [ringModuleOf_bracket]; rw [← map_smul]; rw [← smul_lie]; rw [EquivLike.apply_eq_iff_eq]; rw [← sub_eq_zero]; rw [← sub_lie]
        exact trivial_lie_zero E.proj.ker _ ⟨_, by simp [h.choose_spec _]⟩ (E.toKer m)
      lie_smul r x m := by simp }

/--
lemma `toKer_bracket` / 引理 `toKer_bracket`

English:
lemma toKer_bracket
  given: [IsLieAbelian M] (E : Extension R M L) (x : E.proj.ker) (y : L)
  proof: E.ringModuleOf
    E.toKer ⁅y, E.toKer.symm x⁆ = ⁅E.proj_surjective.hasRightInverse.choose y, x⁆ := by
  simp

中文:
引理 toKer_bracket
  条件: [IsLieAbelian M] (E : 扩张 R M L) (x : E.proj.ker) (y : L)
  证明: E.ringModuleOf
    E.toKer ⁅y, E.toKer.symm x⁆ = ⁅E.proj_surjective.hasRightInverse.choose y, x⁆ := by
  simp

Depends on / 依赖: E.ringModuleOf, ringModuleOf
-/
lemma toKer_bracket [IsLieAbelian M] (E : Extension R M L) (x : E.proj.ker) (y : L) :
    letI := E.ringModuleOf
    E.toKer ⁅y, E.toKer.symm x⁆ = ⁅E.proj_surjective.hasRightInverse.choose y, x⁆ := by
  simp

/--
lemma `lie_apply_proj_of_leftInverse_eq` / 引理 `lie_apply_proj_of_leftInverse_eq`

English:
lemma lie_apply_proj_of_leftInverse_eq
  statement: [IsLieAbelian M] (E : Extension R M L) {s : L ->ₗ[R] E.L}
  proof: by
  rw [← sub_eq_zero]; rw [← sub_lie]
  exact trivial_lie_zero E.proj.ker E.proj.ker ⟨_, (by simp [hs.eq])⟩ y

中文:
引理 lie_apply_proj_of_leftInverse_eq
  结论: [IsLieAbelian M] (E : 扩张 R M L) {s : L ->ₗ[R] E.L}
  证明: by
  rw [← sub_eq_zero]; rw [← sub_lie]
  exact trivial_lie_zero E.proj.ker E.proj.ker ⟨_, (by simp [hs.eq])⟩ y

Depends on / 依赖: E.proj.ker, FinitePresentation, FinitePresentation.of_isBaseChange, LocalizedModule, LocalizedModule.mkLinearMap, hs.eq, isLocalizedModule_iff_isBaseChange, mkLinearMap, of_isBaseChange, sub_eq_zero, sub_lie, trivial_lie_zero
-/
lemma lie_apply_proj_of_leftInverse_eq [IsLieAbelian M] (E : Extension R M L) {s : L ->ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (x : E.L) (y : E.proj.ker) :
    ⁅s (E.proj x), y⁆ = ⁅x, y⁆ := by
  rw [← sub_eq_zero]; rw [← sub_lie]
  exact trivial_lie_zero E.proj.ker E.proj.ker ⟨_, (by simp [hs.eq])⟩ y

set_option backward.privateInPublic true in
/--
Definition of `twoCocycleAux` / `twoCocycleAux` 的定义

English:
abbreviation twoCocycleAux
  signature: (E : Extension R M L) {s : L ->ₗ[R] E.L}
  body: { toFun y := ⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs.eq]⟩
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_sub] }
  map_add' x y := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

中文:
缩写 twoCocycleAux
  签名: (E : 扩张 R M L) {s : L ->ₗ[R] E.L}
  定义体: { toFun y := ⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs.eq]⟩
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_sub] }
  map_add' x y := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]
-/
private abbrev twoCocycleAux (E : Extension R M L) {s : L ->ₗ[R] E.L}
    (hs : LeftInverse E.proj s) :
    L ->ₗ[R] L ->ₗ[R] E.proj.ker where
  toFun x :=
    { toFun y := ⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs.eq]⟩
      map_add' _ _ := by simp; abel
      map_smul' _ _ := by simp [smul_sub] }
  map_add' x y := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The 2-cocycle attached to an extension with a linear section. -/
@[simps]
/--
Definition of `twoCocycleOf` / `twoCocycleOf` 的定义

English:
definition twoCocycleOf
  signature: [IsLieAbelian M] (E : Extension R M L) {s : L ->ₗ[R] E.L}
  body: E.ringModuleOf
    have := E.lieModuleOf
    twoCocycle R L M where
  val := ⟨(E.twoCocycleAux hs).compr₂ E.toKer.symm, by simp⟩
  property := by
    -- TODO Try to golf this after https://github.com/leanprover-community/mathlib4/pull/27306 lands
    ext x y z
    suffices ⁅s x, ⁅s y, s z⁆⁆ - ⁅s x, s ⁅y, z⁆⁆ -
        (⁅s y, ⁅s x, s z⁆⁆ - ⁅s y, s ⁅x, z⁆⁆) + (⁅s z, ⁅s x, s y⁆⁆ - ⁅s z, s ⁅x, y⁆⁆) -
          (⁅s ⁅x, y⁆, s z⁆ - (s ⁅x, ⁅y, z⁆⁆ - s ⁅y, ⁅x, z⁆⁆)) +
        (⁅s ⁅x, z⁆, s y⁆ - (s ⁅x, ⁅z, y⁆⁆ - s ⁅z, ⁅x, y⁆⁆)) -
        (⁅s ⁅y, z⁆, s x⁆ - (s ⁅y, ⁅z, x⁆⁆ - s ⁅z, ⁅y, x⁆⁆)) = 0 by
      set h := E.proj_surjective.hasRightInverse
      have aux (u : L) (v : E.proj.ker) : ⁅h.choose u, v⁆ = ⁅s u, v⁆ := by
        rw [← E.lie_apply_proj_of_leftInverse_eq hs]; rw [h.choose_spec _]
      simpa [← map_sub, ← map_add, ← twoCochain_val_apply, Subtype.ext_iff, twoCocycleAux, aux]
    have hjac := lie_lie (s x) (s y) (s z)
    rw [← lie_skew]; rw [neg_eq_iff_eq_neg] at hjac
    have hja := congr_arg s (lie_lie x y z)
    rw [← lie_skew]; rw [map_neg]; rw [neg_eq_iff_eq_neg] at hja
    have hj := congr_arg s (lie_lie y x z)
    rw [← lie_skew]; rw [map_neg]; rw [neg_eq_iff_eq_neg] at hj
    rw [hjac]; rw [hj]; rw [hja]; rw [← lie_skew y z]; rw [← lie_skew _ (s (-⁅z]; rw [y⁆))]; rw [← lie_skew (s ⁅x]; rw [z⁆)]; rw [← lie_skew (s ⁅x]; rw [y⁆)]; rw [← lie_skew x z]
    simp only [map_neg, neg_lie, neg_neg, neg_sub, lie_neg, sub_neg_eq_add,
      sub_add_cancel_right, map_add, neg_add_rev]
    abel_nf

中文:
定义 twoCocycleOf
  签名: [IsLieAbelian M] (E : 扩张 R M L) {s : L ->ₗ[R] E.L}
  定义体: E.ringModuleOf
    have := E.lieModuleOf
    twoCocycle R L M where
  val := ⟨(E.twoCocycleAux hs).compr₂ E.toKer.symm, by simp⟩
  property := by
    -- TODO Try to golf this after https://github.com/leanprover-community/mathlib4/pull/27306 lands
    ext x y z
    suffices ⁅s x, ⁅s y, s z⁆⁆ - ⁅s x, s ⁅y, z⁆⁆ -
        (⁅s y, ⁅s x, s z⁆⁆ - ⁅s y, s ⁅x, z⁆⁆) + (⁅s z, ⁅s x, s y⁆⁆ - ⁅s z, s ⁅x, y⁆⁆) -
          (⁅s ⁅x, y⁆, s z⁆ - (s ⁅x, ⁅y, z⁆⁆ - s ⁅y, ⁅x, z⁆⁆)) +
        (⁅s ⁅x, z⁆, s y⁆ - (s ⁅x, ⁅z, y⁆⁆ - s ⁅z, ⁅x, y⁆⁆)) -
        (⁅s ⁅y, z⁆, s x⁆ - (s ⁅y, ⁅z, x⁆⁆ - s ⁅z, ⁅y, x⁆⁆)) = 0 by
      set h := E.proj_surjective.hasRightInverse
      have aux (u : L) (v : E.proj.ker) : ⁅h.choose u, v⁆ = ⁅s u, v⁆ := by
        rw [← E.lie_apply_proj_of_leftInverse_eq hs]; rw [h.choose_spec _]
      simpa [← map_sub, ← map_add, ← twoCochain_val_apply, Subtype.ext_iff, twoCocycleAux, aux]
    have hjac := lie_lie (s x) (s y) (s z)
    rw [← lie_skew]; rw [neg_eq_iff_eq_neg] at hjac
    have hja := congr_arg s (lie_lie x y z)
    rw [← lie_skew]; rw [map_neg]; rw [neg_eq_iff_eq_neg] at hja
    have hj := congr_arg s (lie_lie y x z)
    rw [← lie_skew]; rw [map_neg]; rw [neg_eq_iff_eq_neg] at hj
    rw [hjac]; rw [hj]; rw [hja]; rw [← lie_skew y z]; rw [← lie_skew _ (s (-⁅z]; rw [y⁆))]; rw [← lie_skew (s ⁅x]; rw [z⁆)]; rw [← lie_skew (s ⁅x]; rw [y⁆)]; rw [← lie_skew x z]
    simp only [map_neg, neg_lie, neg_neg, neg_sub, lie_neg, sub_neg_eq_add,
      sub_add_cancel_right, map_add, neg_add_rev]
    abel_nf

Depends on / 依赖: E.ringModuleOf, ringModuleOf
-/
noncomputable def twoCocycleOf [IsLieAbelian M] (E : Extension R M L) {s : L ->ₗ[R] E.L}
    (hs : LeftInverse E.proj s) :
    letI := E.ringModuleOf
    have := E.lieModuleOf
    twoCocycle R L M where
  val := ⟨(E.twoCocycleAux hs).compr₂ E.toKer.symm, by simp⟩
  property := by
    -- TODO Try to golf this after https://github.com/leanprover-community/mathlib4/pull/27306 lands
    ext x y z
    suffices ⁅s x, ⁅s y, s z⁆⁆ - ⁅s x, s ⁅y, z⁆⁆ -
        (⁅s y, ⁅s x, s z⁆⁆ - ⁅s y, s ⁅x, z⁆⁆) + (⁅s z, ⁅s x, s y⁆⁆ - ⁅s z, s ⁅x, y⁆⁆) -
          (⁅s ⁅x, y⁆, s z⁆ - (s ⁅x, ⁅y, z⁆⁆ - s ⁅y, ⁅x, z⁆⁆)) +
        (⁅s ⁅x, z⁆, s y⁆ - (s ⁅x, ⁅z, y⁆⁆ - s ⁅z, ⁅x, y⁆⁆)) -
        (⁅s ⁅y, z⁆, s x⁆ - (s ⁅y, ⁅z, x⁆⁆ - s ⁅z, ⁅y, x⁆⁆)) = 0 by
      set h := E.proj_surjective.hasRightInverse
      have aux (u : L) (v : E.proj.ker) : ⁅h.choose u, v⁆ = ⁅s u, v⁆ := by
        rw [← E.lie_apply_proj_of_leftInverse_eq hs]; rw [h.choose_spec _]
      simpa [← map_sub, ← map_add, ← twoCochain_val_apply, Subtype.ext_iff, twoCocycleAux, aux]
    have hjac := lie_lie (s x) (s y) (s z)
    rw [← lie_skew]; rw [neg_eq_iff_eq_neg] at hjac
    have hja := congr_arg s (lie_lie x y z)
    rw [← lie_skew]; rw [map_neg]; rw [neg_eq_iff_eq_neg] at hja
    have hj := congr_arg s (lie_lie y x z)
    rw [← lie_skew]; rw [map_neg]; rw [neg_eq_iff_eq_neg] at hj
    rw [hjac]; rw [hj]; rw [hja]; rw [← lie_skew y z]; rw [← lie_skew _ (s (-⁅z]; rw [y⁆))]; rw [← lie_skew (s ⁅x]; rw [z⁆)]; rw [← lie_skew (s ⁅x]; rw [y⁆)]; rw [← lie_skew x z]
    simp only [map_neg, neg_lie, neg_neg, neg_sub, lie_neg, sub_neg_eq_add,
      sub_add_cancel_right, map_add, neg_add_rev]
    abel_nf

/-- The 1-cochain attached to a pair of splittings of an extension. -/
@[simps]
/--
Definition of `oneCochainOfTwoSplitting` / `oneCochainOfTwoSplitting` 的定义

English:
definition oneCochainOfTwoSplitting
  signature: (E : Extension R M L) {s₁ s₂ : L ->ₗ[R] E.L}
  body: E.toKer.symm ⟨(s₁ x) - (s₂ x), LieHom.mem_ker.mpr (by rw [map_sub, sub_eq_zero, hs₁, hs₂])⟩
  map_add' _ _ := by
    rw [← map_add]; rw [AddMemClass.mk_add_mk]; rw [EquivLike.apply_eq_iff_eq]; rw [Subtype.mk_eq_mk]; rw [map_add]; rw [map_add]; rw [add_sub_add_comm]
  map_smul' _ _ := by
    rw [RingHom.id_apply]; rw [← map_smul]; rw [EquivLike.apply_eq_iff_eq]; rw [SetLike.mk_smul_of_tower_mk]; rw [Subtype.mk_eq_mk]; rw [LinearMap.map_smul_of_tower]; rw [smul_sub]; rw [LinearMap.map_smul_of_tower]

中文:
定义 oneCochainOfTwoSplitting
  签名: (E : 扩张 R M L) {s₁ s₂ : L ->ₗ[R] E.L}
  定义体: E.toKer.symm ⟨(s₁ x) - (s₂ x), LieHom.mem_ker.mpr (by rw [map_sub, sub_eq_zero, hs₁, hs₂])⟩
  map_add' _ _ := by
    rw [← map_add]; rw [AddMemClass.mk_add_mk]; rw [EquivLike.apply_eq_iff_eq]; rw [Subtype.mk_eq_mk]; rw [map_add]; rw [map_add]; rw [add_sub_add_comm]
  map_smul' _ _ := by
    rw [RingHom.id_apply]; rw [← map_smul]; rw [EquivLike.apply_eq_iff_eq]; rw [SetLike.mk_smul_of_tower_mk]; rw [Subtype.mk_eq_mk]; rw [LinearMap.map_smul_of_tower]; rw [smul_sub]; rw [LinearMap.map_smul_of_tower]

Depends on / 依赖: AddMemClass, AddMemClass.mk_add_mk, E.toKer.symm, EquivLike, EquivLike.apply_eq_iff_eq, LieHom, LieHom.mem_ker.mpr, LinearMap, LinearMap.map_smul_of_tower, RingHom, RingHom.id_apply, SetLike, SetLike.mk_smul_of_tower_mk, Subtype, Subtype.mk_eq_mk, add_sub_add_comm, apply_eq_iff_eq, id_apply, map_add, map_smul
-/
noncomputable def oneCochainOfTwoSplitting (E : Extension R M L) {s₁ s₂ : L ->ₗ[R] E.L}
    (hs₁ : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂) :
    oneCochain R L M where
  toFun x :=
    E.toKer.symm ⟨(s₁ x) - (s₂ x), LieHom.mem_ker.mpr (by rw [map_sub, sub_eq_zero, hs₁, hs₂])⟩
  map_add' _ _ := by
    rw [← map_add]; rw [AddMemClass.mk_add_mk]; rw [EquivLike.apply_eq_iff_eq]; rw [Subtype.mk_eq_mk]; rw [map_add]; rw [map_add]; rw [add_sub_add_comm]
  map_smul' _ _ := by
    rw [RingHom.id_apply]; rw [← map_smul]; rw [EquivLike.apply_eq_iff_eq]; rw [SetLike.mk_smul_of_tower_mk]; rw [Subtype.mk_eq_mk]; rw [LinearMap.map_smul_of_tower]; rw [smul_sub]; rw [LinearMap.map_smul_of_tower]

/--
lemma `d₁₂_oneCochainOfTwoSplitting` / 引理 `d₁₂_oneCochainOfTwoSplitting`

English:
lemma d₁₂_oneCochainOfTwoSplitting
  statement: [IsLieAbelian M] (E : Extension R M L) {s₁ s₂ : L ->ₗ[R] E.L}
  proof: E.ringModuleOf
    letI := E.lieModuleOf
    d₁₂ R L M (E.oneCochainOfTwoSplitting hs₁ hs₂) = E.twoCocycleOf hs₁ - E.twoCocycleOf hs₂ := by
  ext x y
  choose s hs using E.proj_surjective
  have {s' : L -> E.L} (h : LeftInverse E.proj s') : ⁅s x - s' x, s' y - s y⁆ = (0 : E.L) := by
    have aux := trivial_lie_zero E.proj.ker E.proj.ker
      ⟨s x - s' x, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
      ⟨s' y - s y, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
    simpa only [Subtype.ext_iff, LieSubmodule.coe_zero, LieIdeal.coe_bracket_of_module,
      LieSubmodule.coe_bracket] using aux
  replace this {s' : L -> E.L} (h : LeftInverse E.proj s') :
      ⁅s x, s' y⁆ = ⁅s' x, s' y⁆ + (⁅s x, s y⁆ - ⁅s' x, s y⁆) := by
    simpa [sub_sub, sub_eq_zero] using this h
  simp only [d₁₂_apply_coe_apply_apply, oneCochainOfTwoSplitting_apply, AddSubgroupClass.coe_sub,
    twoCocycleOf_coe_coe, LinearMap.sub_apply, LinearMap.compr₂_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  nth_rw 1 [← hs x]
  nth_rw 4 [← hs y]
  simp only [← EmbeddingLike.apply_eq_iff_eq E.toKer, ringModuleOf_bracket_proj,
    LieEquiv.apply_symm_apply, map_sub, Subtype.ext_iff, AddSubgroupClass.coe_sub,
    LieSubmodule.coe_bracket, lie_sub, this hs₁, this hs₂, ← lie_skew (s₁ x) (s y),
    ← lie_skew (s₂ x) (s y)]
  abel

中文:
引理 d₁₂_oneCochainOfTwoSplitting
  结论: [IsLieAbelian M] (E : 扩张 R M L) {s₁ s₂ : L ->ₗ[R] E.L}
  证明: E.ringModuleOf
    letI := E.lieModuleOf
    d₁₂ R L M (E.oneCochainOfTwoSplitting hs₁ hs₂) = E.twoCocycleOf hs₁ - E.twoCocycleOf hs₂ := by
  ext x y
  choose s hs using E.proj_surjective
  have {s' : L -> E.L} (h : LeftInverse E.proj s') : ⁅s x - s' x, s' y - s y⁆ = (0 : E.L) := by
    have aux := trivial_lie_zero E.proj.ker E.proj.ker
      ⟨s x - s' x, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
      ⟨s' y - s y, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
    simpa only [Subtype.ext_iff, LieSubmodule.coe_zero, LieIdeal.coe_bracket_of_module,
      LieSubmodule.coe_bracket] using aux
  replace this {s' : L -> E.L} (h : LeftInverse E.proj s') :
      ⁅s x, s' y⁆ = ⁅s' x, s' y⁆ + (⁅s x, s y⁆ - ⁅s' x, s y⁆) := by
    simpa [sub_sub, sub_eq_zero] using this h
  simp only [d₁₂_apply_coe_apply_apply, oneCochainOfTwoSplitting_apply, AddSubgroupClass.coe_sub,
    twoCocycleOf_coe_coe, LinearMap.sub_apply, LinearMap.compr₂_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  nth_rw 1 [← hs x]
  nth_rw 4 [← hs y]
  simp only [← EmbeddingLike.apply_eq_iff_eq E.toKer, ringModuleOf_bracket_proj,
    LieEquiv.apply_symm_apply, map_sub, Subtype.ext_iff, AddSubgroupClass.coe_sub,
    LieSubmodule.coe_bracket, lie_sub, this hs₁, this hs₂, ← lie_skew (s₁ x) (s y),
    ← lie_skew (s₂ x) (s y)]
  abel

Depends on / 依赖: E.ringModuleOf, ringModuleOf
-/
lemma d₁₂_oneCochainOfTwoSplitting [IsLieAbelian M] (E : Extension R M L) {s₁ s₂ : L ->ₗ[R] E.L}
    (hs₁ : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂) :
    letI := E.ringModuleOf
    letI := E.lieModuleOf
    d₁₂ R L M (E.oneCochainOfTwoSplitting hs₁ hs₂) = E.twoCocycleOf hs₁ - E.twoCocycleOf hs₂ := by
  ext x y
  choose s hs using E.proj_surjective
  have {s' : L -> E.L} (h : LeftInverse E.proj s') : ⁅s x - s' x, s' y - s y⁆ = (0 : E.L) := by
    have aux := trivial_lie_zero E.proj.ker E.proj.ker
      ⟨s x - s' x, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
      ⟨s' y - s y, by rw [LieHom.mem_ker, map_sub, sub_eq_zero, h, hs]⟩
    simpa only [Subtype.ext_iff, LieSubmodule.coe_zero, LieIdeal.coe_bracket_of_module,
      LieSubmodule.coe_bracket] using aux
  replace this {s' : L -> E.L} (h : LeftInverse E.proj s') :
      ⁅s x, s' y⁆ = ⁅s' x, s' y⁆ + (⁅s x, s y⁆ - ⁅s' x, s y⁆) := by
    simpa [sub_sub, sub_eq_zero] using this h
  simp only [d₁₂_apply_coe_apply_apply, oneCochainOfTwoSplitting_apply, AddSubgroupClass.coe_sub,
    twoCocycleOf_coe_coe, LinearMap.sub_apply, LinearMap.compr₂_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  nth_rw 1 [← hs x]
  nth_rw 4 [← hs y]
  simp only [← EmbeddingLike.apply_eq_iff_eq E.toKer, ringModuleOf_bracket_proj,
    LieEquiv.apply_symm_apply, map_sub, Subtype.ext_iff, AddSubgroupClass.coe_sub,
    LieSubmodule.coe_bracket, lie_sub, this hs₁, this hs₂, ← lie_skew (s₁ x) (s y),
    ← lie_skew (s₂ x) (s y)]
  abel

end LieAlgebra.Extension
