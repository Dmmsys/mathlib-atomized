/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.Basic

/-!
# Direct sums of Lie algebras and Lie modules

Direct sums of Lie algebras and Lie modules carry natural algebra and module structures.

## Tags

lie algebra, lie module, direct sum
-/

@[expose] public section


universe u v w w₁

namespace DirectSum

open DFinsupp

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

section Modules

/-! The direct sum of Lie modules over a fixed Lie algebra carries a natural Lie module
structure. -/


variable {L : Type w₁} {M : ι → Type w}
variable [LieRing L] [LieAlgebra R L]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]

/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRingModule L (⨁ i, M i) where
  bracket x m := m.mapRange (fun _ m' => ⁅x, m'⁆) fun _ => lie_zero x
  add_lie x y m := by
    ext
    simp only [mapRange_apply, add_apply, add_lie]
  lie_add x m n := by
    ext
    simp only [mapRange_apply, add_apply, lie_add]
  leibniz_lie x y m := by
    ext
    simp only [mapRange_apply, lie_lie, add_apply, sub_add_cancel]

@[simp]
/-
**DirectSum.lie_module_bracket_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x, m⁆ i = ⁅x, m
 i⁆
参数：x : L；m : ⨁ i, M i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_apply`：mapRange_apply (f : forall i, β₁ i -> β₂ i) (hf
 : forall i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) : mapRange f hf g i = f i (g i)
-/
theorem lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x, m⁆ i = ⁅x, m i⁆ :=
  mapRange_apply _ _ m i
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule R L (⨁ i, M i) where
  smul_lie t x m := by
    ext
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
  lie_smul t x m := by
    ext
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]

variable (R ι L M)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of each component into a direct sum as a morphism of Lie modules. -/
/-
**DirectSum.lieModuleOf** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lieModuleOf [DecidableEq ι] (j : ι) : M j ->ₗ⁅R,L⁆ ⨁ i, M i
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of each component into a direct sum as a morphism of Lie modules.
-/
def lieModuleOf [DecidableEq ι] (j : ι) : M j →ₗ⁅R,L⁆ ⨁ i, M i :=
  { lof R ι M j with
    map_lie' := fun {x m} => by
      ext i
      by_cases h : j = i
      · rw [← h]; simp
      · -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
        -- old proof `simp [lof, lsingle, h]`
        simp only [lof, lsingle, AddHom.toFun_eq_coe, lie_module_bracket_apply]
        -- The coercion in the goal is `DFunLike.coe (β := fun x ↦ Π₀ (i : ι), M i)`
        -- but the lemma is expecting `DFunLike.coe (β := fun x ↦ ⨁ (i : ι), M i)`
        erw [AddHom.coe_mk]
        simp [h] }

set_option backward.isDefEq.respectTransparency false in
/-- The projection map onto one component, as a morphism of Lie modules. -/
/-
**DirectSum.lieModuleComponent** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lieModuleComponent (j : ι) : (⨁ i, M i) ->ₗ⁅R,L⁆ M j
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map onto one component, as a morphism of Lie modules.
-/
def lieModuleComponent (j : ι) : (⨁ i, M i) →ₗ⁅R,L⁆ M j :=
  { component R ι M j with
    map_lie' := fun {x m} => by simp [component, lapply] }

end Modules

section Algebras

/-! The direct sum of Lie algebras carries a natural Lie algebra structure. -/


variable (L : ι → Type w)
variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.lieRing** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：lieRing : LieRing (⨁ i, L i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieRing : LieRing (⨁ i, L i) :=
  { (inferInstance : AddCommGroup _) with
    bracket := zipWith (fun _ => fun x y => ⁅x, y⁆) fun _ => lie_zero 0
    add_lie := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, add_lie]
    lie_add := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, lie_add]
    lie_self := fun x => by
      ext
      simp only [zipWith_apply, lie_self, zero_apply]
    leibniz_lie := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply]
      apply leibniz_lie }

@[simp]
/-
**DirectSum.bracket_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆
参数：x y : ⨁ i, L i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.zipWith_apply`：zipWith_apply (f : forall i, β₁ i -> β₂ i -> β i
) (hf : forall i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) (i : ι) : zip
With f hf g₁…
-/
theorem bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ :=
  zipWith_apply _ _ x y i
/-
**DirectSum.lie_of_same** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lie_of_same [DecidableEq ι] {i : ι} (x y : L i) : ⁅of L i x, of L i y⁆ = o
f L i ⁅x, y⁆
参数：x y : L i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.zipWith_single_single`：zipWith_single_single (f : forall i, β₁ 
i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) {i} (b₁ : β₁ i) (b₂ : β₂ i) : zip
With f hf (single i …
-/
theorem lie_of_same [DecidableEq ι] {i : ι} (x y : L i) :
    ⁅of L i x, of L i y⁆ = of L i ⁅x, y⁆ :=
  DFinsupp.zipWith_single_single _ _ _ _
/-
**DirectSum.lie_of_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : i != j) (x : L i) (y : L j) 
: ⁅of L i x, of L j y⁆ = 0
参数：hij : i != j；x : L i；y : L j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.bracket_apply`：bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆
 i = ⁅x i, y i⁆
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `DirectSum.zero_apply`：zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
-/
theorem lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : i ≠ j) (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = 0 := by
  ext k
  rw [bracket_apply]
  obtain rfl | hik := Decidable.eq_or_ne k i
  · rw [of_eq_of_ne _ _ _ hij, lie_zero, zero_apply]
  · rw [of_eq_of_ne _ _ _ hik, zero_lie, zero_apply]

@[simp]
/-
**DirectSum.lie_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) : ⁅of L i x, of L j y
⁆ = if hij : i = j then of L i ⁅x, hij.symm.recOn y⁆ else 0
参数：x : L i；y : L j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.lie_of_same`：lie_of_same [DecidableEq ι] {i : ι} (x y : L i) :
 ⁅of L i x, of L i y⁆ = of L i ⁅x, y⁆
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `DirectSum.lie_of_of_ne`：lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : i 
!= j) (x : L i) (y : L j) : ⁅of L i x, of L j y⁆ = 0
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = if hij : i = j then of L i ⁅x, hij.symm.recOn y⁆ else 0 := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp only [lie_of_same L x y, dif_pos]
  · simp only [lie_of_of_ne L hij x y, hij, dite_false]
/-
**DirectSum.lieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：lieAlgebra : LieAlgebra R (⨁ i, L i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieAlgebra : LieAlgebra R (⨁ i, L i) :=
  { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      ext
      simp only [smul_apply, bracket_apply, lie_smul] }

variable (R ι)

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
@[simps]
/-
**DirectSum.lieAlgebraOf** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lieAlgebraOf [DecidableEq ι] (j : ι) : L j ->ₗ⁅R⁆ ⨁ i, L i
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of each component into the direct sum as morphism of Lie algebras.
-/
def lieAlgebraOf [DecidableEq ι] (j : ι) : L j →ₗ⁅R⁆ ⨁ i, L i :=
  { lof R ι L j with
    toFun := of L j
    map_lie' := fun {x y} => (lie_of_same L x y).symm }

set_option backward.isDefEq.respectTransparency false in
/-- The projection map onto one component, as a morphism of Lie algebras. -/
@[simps]
/-
**DirectSum.lieAlgebraComponent** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lieAlgebraComponent (j : ι) : (⨁ i, L i) ->ₗ⁅R⁆ L j
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map onto one component, as a morphism of Lie algebras.
-/
def lieAlgebraComponent (j : ι) : (⨁ i, L i) →ₗ⁅R⁆ L j :=
  { component R ι L j with
    toFun := component R ι L j
    map_lie' := fun {x y} => by simp [component, lapply] }

-- Note(kmill): `ext` cannot generate an iff theorem here since `x` and `y` do not determine `R`.
@[ext (iff := false)]
/-
**DirectSum.lieAlgebra_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lieAlgebra_ext {x y : ⨁ i, L i} (h : forall i, lieAlgebraComponent R ι L i
 x = lieAlgebraComponent R ι L i y) : x = y
参数：h : forall i, lieAlgebraComponent R ι L i x = lieAlgebraComponent R ι L i y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem lieAlgebra_ext {x y : ⨁ i, L i}
    (h : ∀ i, lieAlgebraComponent R ι L i x = lieAlgebraComponent R ι L i y) : x = y :=
  DFinsupp.ext h

variable {R L ι}

/-- Given a family of Lie algebras `L i`, together with a family of morphisms of Lie algebras
`f i : L i →ₗ⁅R⁆ L'` into a fixed Lie algebra `L'`, we have a natural linear map:
`(⨁ i, L i) →ₗ[R] L'`. If in addition `⁅f i x, f j y⁆ = 0` for any `x ∈ L i` and `y ∈ L j` (`i ≠ j`)
then this map is a morphism of Lie algebras. -/
@[simps]
/-
**DirectSum.toLieAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：toLieAlgebra [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
 (f : forall i, L i ->ₗ⁅R⁆ L') (hf : Pairwise fun i j => forall (x : L i) (y : L
 j), ⁅f i x, f j y⁆ = 0) : (⨁ i, L i) ->ₗ⁅R⁆ L'
参数：L' : Type w₁；f : forall i, L i ->ₗ⁅R⁆ L'；hf : Pairwise fun i j => forall (x :
 L i) (y : L j), ⁅f i x, f j y⁆ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of Lie algebras `L i`, together with a family of morphisms of Lie
 algebras
`f i : L i →ₗ⁅R⁆ L'` into a fixed Lie algebra `L'`, we have a natural linear map
:
`(⨁ i, L i) →ₗ[R] L'`. If in addition `⁅f i x, f j y⁆ = 0` for any `x ∈ L i` and
 `y ∈ L j` (`i ≠ j`)
then this map is a morphism of Lie algebras.
-/
def toLieAlgebra [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
    (f : ∀ i, L i →ₗ⁅R⁆ L') (hf : Pairwise fun i j => ∀ (x : L i) (y : L j), ⁅f i x, f j y⁆ = 0) :
    (⨁ i, L i) →ₗ⁅R⁆ L' :=
  { toModule R ι L' fun i => (f i : L i →ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i →ₗ[R] L')
    map_lie' := fun {x y} => by
      let f' i := (f i : L i →ₗ[R] L')
      /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
        non-zero component. -/
      suffices ∀ (i : ι) (y : L i),
          toModule R ι L' f' ⁅x, of L i y⁆ =
            ⁅toModule R ι L' f' x, toModule R ι L' f' (of L i y)⁆ by
        simp only [← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr; clear y; ext i y; exact this i y
      -- Similarly, we can reduce to the case that `x` has only one non-zero component.
      suffices ∀ (i j) (y : L i) (x : L j),
          toModule R ι L' f' ⁅of L j x, of L i y⁆ =
            ⁅toModule R ι L' f' (of L j x), toModule R ι L' f' (of L i y)⁆ by
        intro i y
        rw [← lie_skew x, ← lie_skew (toModule R ι L' f' x)]
        simp only [map_neg, neg_inj, ← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr; clear x; ext j x; exact this j i x y
      intro i j y x
      simp only [f', coe_toModule_eq_coe_toAddMonoid, toAddMonoid_of]
      -- And finish with trivial case analysis.
      obtain rfl | hij := Decidable.eq_or_ne i j
      · simp_rw [lie_of_same, toAddMonoid_of, LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap,
          LieHom.map_lie]
      · simp_rw [lie_of_of_ne _ hij.symm, map_zero, LinearMap.toAddMonoidHom_coe,
          LieHom.coe_toLinearMap, hf hij.symm x y] }

end Algebras

section Ideals

variable {L : Type w} [LieRing L] [LieAlgebra R L] (I : ι → LieIdeal R L)

/-- The fact that this instance is necessary seems to be a bug in typeclass inference. See
[this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/245151099). -/
/-
**DirectSum.lieRingOfIdeals** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：lieRingOfIdeals : LieRing (⨁ i, I i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fact that this instance is necessary seems to be a bug in typeclass inferenc
e. See
[this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-gener
al/topic/Typeclass.20resolution.20under.20binders/near/245151099).
-/
instance lieRingOfIdeals : LieRing (⨁ i, I i) :=
  DirectSum.lieRing fun i => ↥(I i)

/-- See `DirectSum.lieRingOfIdeals` comment. -/
/-
**DirectSum.lieAlgebraOfIdeals** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：lieAlgebraOfIdeals : LieAlgebra R (⨁ i, I i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `DirectSum.lieRingOfIdeals` comment.
-/
instance lieAlgebraOfIdeals : LieAlgebra R (⨁ i, I i) :=
  DirectSum.lieAlgebra fun i => ↥(I i)

end Ideals

end DirectSum

