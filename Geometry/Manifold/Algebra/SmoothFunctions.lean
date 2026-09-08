/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Algebraic structures over `C^n` functions

In this file, we define instances of algebraic structures over `C^n` functions.
-/

@[expose] public section


noncomputable section

open scoped Manifold ContDiff

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {N' : Type*} [TopologicalSpace N'] [ChartedSpace H'' N']
  {n : ℕ∞ω}

namespace ContMDiffMap

@[to_additive]
/-
**ContMDiffMap.instMul** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {E' : Type u_3} →             [inst_3 : NormedAddCommGroup E'] →      
         [inst_4 : NormedSpace 𝕜 E'] →                 {H : Type u_4} →         
          [inst_5 : TopologicalSpace H] →                     {I : ModelWithCorn
ers 𝕜 E H} →                       {H' : Type u_5} →                         [in
st_6 : TopologicalSpace H'] →                           {I' : ModelWithCorners 𝕜
 E' H'} →                             {N : Type u_6} →                          
     [inst_7 : TopologicalSpace N] →                                 [inst_8 : C
hartedSpace H N] →                                   {n : WithTop ℕ∞} →         
                            {G : Type u_10} →                                   
    [inst_9 : Mul G] →                                         [inst_10 : Topolo
gicalSpace G] →                                           [inst_11 : ChartedSpac
e H' G] →                                             [ContMDiffMul I' n G] → Mu
l (ContMDiffMap I I' N G n)
参数：ContMDiffMap I I' N G n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance instMul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Mul C^n⟮I, N; I', G⟯ :=
  ⟨fun f g => ⟨f * g, f.contMDiff.mul g.contMDiff⟩⟩

@[to_additive (attr := simp)]
/-
**ContMDiffMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [Cont
MDiffMul I' n G] (f g : C^n⟮I, N; I', G⟯) : ⇑(f * g) = f * g
参数：f g : C^n⟮I, N; I', G⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
/-
**ContMDiffMap.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：mul_comp {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [Con
tMDiffMul I' n G] (f g : C^n⟮I'', N'; I', G⟯) (h : C^n⟮I, N; I'', N'⟯) : (f * g)
.comp h = f.comp h * g.comp h
参数：f g : C^n⟮I'', N'; I', G⟯；h : C^n⟮I, N; I'', N'⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_comp {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffMul I' n G]
    (f g : C^n⟮I'', N'; I', G⟯) (h : C^n⟮I, N; I'', N'⟯) : (f * g).comp h = f.comp h * g.comp h :=
  rfl

@[to_additive]
/-
**ContMDiffMap.instOne** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {E' : Type u_3} →             [inst_3 : NormedAddCommGroup E'] →      
         [inst_4 : NormedSpace 𝕜 E'] →                 {H : Type u_4} →         
          [inst_5 : TopologicalSpace H] →                     {I : ModelWithCorn
ers 𝕜 E H} →                       {H' : Type u_5} →                         [in
st_6 : TopologicalSpace H'] →                           {I' : ModelWithCorners 𝕜
 E' H'} →                             {N : Type u_6} →                          
     [inst_7 : TopologicalSpace N] →                                 [inst_8 : C
hartedSpace H N] →                                   {n : WithTop ℕ∞} →         
                            {G : Type u_10} →                                   
    [One G] →                                         [inst_10 : TopologicalSpac
e G] →                                           [inst_11 : ChartedSpace H' G] →
 One (ContMDiffMap I I' N G n)
参数：ContMDiffMap I I' N G n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance instOne {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    One C^n⟮I, N; I', G⟯ :=
  ⟨ContMDiffMap.const (1 : G)⟩

@[to_additive (attr := simp)]
/-
**ContMDiffMap.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_one {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] : ⇑(1
 : C^n⟮I, N; I', G⟯) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one {G : Type*} [One G] [TopologicalSpace G] [ChartedSpace H' G] :
    ⇑(1 : C^n⟮I, N; I', G⟯) = 1 :=
  rfl

@[to_additive]
/-
**ContMDiffMap.instPow** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：instPow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G] [C
ontMDiffMul I' n G] : Pow C^n⟮I, N; I', G⟯ Nat where pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] :
    Pow C^n⟮I, N; I', G⟯ ℕ where
  pow f n := ⟨(f : N → G) ^ n, (contMDiff_pow n).comp f.contMDiff⟩

@[to_additive (attr := simp)]
/-
**ContMDiffMap.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_pow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G] [C
ontMDiffMul I' n G] (f : C^n⟮I, N; I', G⟯) (n : Nat) : ⇑(f ^ n) = (f : N -> G) ^
 n
参数：f : C^n⟮I, N; I', G⟯；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] (f : C^n⟮I, N; I', G⟯) (n : ℕ) :
    ⇑(f ^ n) = (f : N → G) ^ n :=
  rfl

section GroupStructure

/-!
### Group structure

In this section we show that `C^n` functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

@[to_additive]
/-
**ContMDiffMap.semigroup** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：semigroup {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' 
G] [ContMDiffMul I' n G] : Semigroup C^n⟮I, N; I', G⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Group structure

In this section we show that `C^n` functions valued in a Lie group inherit a gro
up structure
under pointwise multiplication.
-/
instance semigroup {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Semigroup C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.semigroup _ coe_mul

@[to_additive]
/-
**ContMDiffMap.monoid** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：monoid {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G] [Co
ntMDiffMul I' n G] : Monoid C^n⟮I, N; I', G⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.coe_pow`：coe_pow {G : Type*} [Monoid G] [TopologicalSpace G
] [ChartedSpace H' G] [ContMDiffMul I' n G] (f : C^n⟮I, N; I', G⟯) (n : Nat) : ⇑
(f ^ n) = …
-/
instance monoid {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : Monoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.monoid _ coe_one coe_mul coe_pow

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps) /-- Coercion to a function as an `AddMonoidHom`.
  Similar to `AddMonoidHom.coeFn`. -/]
/-
**ContMDiffMap.coeFnMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：coeFnMonoidHom {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H
' G] [ContMDiffMul I' n G] : C^n⟮I, N; I', G⟯ ->* N -> G where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coeFnMonoidHom {G : Type*} [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : C^n⟮I, N; I', G⟯ →* N → G where
  toFun := DFunLike.coe
  map_one' := coe_one
  map_mul' := coe_mul

variable (I N)

/-- For a manifold `N` and a `C^n` homomorphism `φ` between Lie groups `G'`, `G''`, the
'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to `C^n⟮I, N; I'', G''⟯`. -/
@[to_additive /-- For a manifold `N` and a `C^n` homomorphism `φ` between additive Lie groups `G'`,
`G''`, the 'left-composition-by-`φ`' group homomorphism from `C^n⟮I, N; I', G'⟯` to
`C^n⟮I, N; I'', G''⟯`. -/]
/-
**ContMDiffMap.compLeftMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：compLeftMonoidHom {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedS
pace H' G'] [ContMDiffMul I' n G'] {G'' : Type*} [Monoid G''] [TopologicalSpace 
G''] [ChartedSpace H'' G''] [ContMDiffMul I'' n G''] (φ : G' ->* G'') (hφ : CMDi
ff n φ) : C^n⟮I, N; I', G'⟯ ->* C^n⟮I, N; I'', G''⟯ where toFun f
参数：φ : G' ->* G''；hφ : CMDiff n φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compLeftMonoidHom {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G']
    [ContMDiffMul I' n G'] {G'' : Type*} [Monoid G''] [TopologicalSpace G''] [ChartedSpace H'' G'']
    [ContMDiffMul I'' n G''] (φ : G' →* G'') (hφ : CMDiff n φ) :
    C^n⟮I, N; I', G'⟯ →* C^n⟮I, N; I'', G''⟯ where
  toFun f := ⟨φ ∘ f, hφ.comp f.contMDiff⟩
  map_one' := by ext; change φ 1 = 1; simp
  map_mul' f g := by ext x; change φ (f x * g x) = φ (f x) * φ (g x); simp

variable (I') {N}

-- TODO: generalize to any `C^n` map instead of `Set.inclusion`
/-- For a Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction' group homomorphism from
`C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/
@[to_additive /-- For an additive Lie group `G` and open sets `U ⊆ V` in `N`, the 'restriction'
group homomorphism from `C^n⟮I, V; I', G⟯` to `C^n⟮I, U; I', G⟯`. -/]
/-
**ContMDiffMap.restrictMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpac
e H' G] [ContMDiffMul I' n G] {U V : Opens N} (h : U <= V) : C^n⟮I, V; I', G⟯ ->
* C^n⟮I, U; I', G⟯ where toFun f
参数：G : Type*；h : U <= V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def restrictMonoidHom (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] {U V : Opens N} (h : U ≤ V) : C^n⟮I, V; I', G⟯ →* C^n⟮I, U; I', G⟯ where
  toFun f := ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I I'}

@[to_additive]
/-
**ContMDiffMap.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：commMonoid {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H
' G] [ContMDiffMul I' n G] : CommMonoid C^n⟮I, N; I', G⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffMul I' n G] : CommMonoid C^n⟮I, N; I', G⟯ :=
  DFunLike.coe_injective.commMonoid _ coe_one coe_mul coe_pow

@[to_additive]
/-
**ContMDiffMap.group** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：group {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieG
roup I' n G] : Group C^n⟮I, N; I', G⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
-/
instance group {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G] :
    Group C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.monoid with
    inv := fun f => ⟨fun x => (f x)⁻¹, f.contMDiff.inv⟩
    inv_mul_cancel := fun a => by ext; exact inv_mul_cancel _
    div := fun f g => ⟨f / g, f.contMDiff.div g.contMDiff⟩
    div_eq_mul_inv := fun f g => by ext; exact div_eq_mul_inv _ _ }

@[to_additive (attr := simp)]
/-
**ContMDiffMap.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_inv {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [Li
eGroup I' n G] (f : C^n⟮I, N; I', G⟯) : ⇑f⁻¹ = (⇑f)⁻¹
参数：f : C^n⟮I, N; I', G⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f : C^n⟮I, N; I', G⟯) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**ContMDiffMap.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_div {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [Li
eGroup I' n G] (f g : C^n⟮I, N; I', G⟯) : ⇑(f / g) = f / g
参数：f g : C^n⟮I, N; I', G⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G] [LieGroup I' n G]
    (f g : C^n⟮I, N; I', G⟯) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
/-
**ContMDiffMap.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：commGroup {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' 
G] [LieGroup I' n G] : CommGroup C^n⟮I, N; I', G⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGroup {G : Type*} [CommGroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I' n G] : CommGroup C^n⟮I, N; I', G⟯ :=
  { ContMDiffMap.group, ContMDiffMap.commMonoid with }

end GroupStructure

section RingStructure

/-!
### Ring structure

In this section we show that `C^n` functions valued in a `C^n` ring `R` inherit a ring structure
under pointwise multiplication.
-/


/-
**ContMDiffMap.semiring** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：semiring {R : Type*} [Semiring R] [TopologicalSpace R] [ChartedSpace H' R]
 [ContMDiffRing I' n R] : Semiring C^n⟮I, N; I', R⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffRing.toContMDiffAdd`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…

--- 原说明 ---
### Ring structure

In this section we show that `C^n` functions valued in a `C^n` ring `R` inherit 
a ring structure
under pointwise multiplication.
-/
instance semiring {R : Type*} [Semiring R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : Semiring C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.addCommMonoid,
    ContMDiffMap.monoid with
    left_distrib := fun a b c => by ext; exact left_distrib _ _ _
    right_distrib := fun a b c => by ext; exact right_distrib _ _ _
    zero_mul := fun a => by ext; exact zero_mul _
    mul_zero := fun a => by ext; exact mul_zero _ }
/-
**ContMDiffMap.ring** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：ring {R : Type*} [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [ContMD
iffRing I' n R] : Ring C^n⟮I, N; I', R⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffRing.toLieAddGroup`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 :
 NormedAddCommGro…
-/
instance ring {R : Type*} [Ring R] [TopologicalSpace R] [ChartedSpace H' R] [ContMDiffRing I' n R] :
    Ring C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.semiring, ContMDiffMap.addCommGroup with }
/-
**ContMDiffMap.commRing** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：commRing {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
 [ContMDiffRing I' n R] : CommRing C^n⟮I, N; I', R⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : CommRing C^n⟮I, N; I', R⟯ :=
  { ContMDiffMap.semiring, ContMDiffMap.addCommGroup, ContMDiffMap.commMonoid with }

variable (I N)

/-- For a manifold `N` and a `C^n` homomorphism `φ` between `C^n` rings `R'`, `R''`, the
'left-composition-by-`φ`' ring homomorphism from `C^n⟮I, N; I', R'⟯` to `C^n⟮I, N; I'', R''⟯`. -/
/-
**ContMDiffMap.compLeftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：compLeftRingHom {R' : Type*} [Ring R'] [TopologicalSpace R'] [ChartedSpace
 H' R'] [ContMDiffRing I' n R'] {R'' : Type*} [Ring R''] [TopologicalSpace R''] 
[ChartedSpace H'' R''] [ContMDiffRing I'' n R''] (φ : R' ->+* R'') (hφ : CMDiff 
n φ) : C^n⟮I, N; I', R'⟯ ->+* C^n⟮I, N; I'', R''⟯
参数：φ : R' ->+* R''；hφ : CMDiff n φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a manifold `N` and a `C^n` homomorphism `φ` between `C^n` rings `R'`, `R''`,
 the
'left-composition-by-`φ`' ring homomorphism from `C^n⟮I, N; I', R'⟯` to `C^n⟮I, 
N; I'', R''⟯`.
-/
def compLeftRingHom {R' : Type*} [Ring R'] [TopologicalSpace R'] [ChartedSpace H' R']
    [ContMDiffRing I' n R'] {R'' : Type*} [Ring R''] [TopologicalSpace R''] [ChartedSpace H'' R'']
    [ContMDiffRing I'' n R''] (φ : R' →+* R'') (hφ : CMDiff n φ) :
    C^n⟮I, N; I', R'⟯ →+* C^n⟮I, N; I'', R''⟯ :=
  { ContMDiffMap.compLeftMonoidHom I N φ.toMonoidHom hφ,
    ContMDiffMap.compLeftAddMonoidHom I N φ.toAddMonoidHom hφ with
    toFun := fun f => ⟨φ ∘ f, hφ.comp f.contMDiff⟩ }

variable (I') {N}

/-- For a "`C^n` ring" `R` and open sets `U ⊆ V` in `N`, the "restriction" ring homomorphism from
`C^n⟮I, V; I', R⟯` to `C^n⟮I, U; I', R⟯`. -/
/-
**ContMDiffMap.restrictRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：restrictRingHom (R : Type*) [Ring R] [TopologicalSpace R] [ChartedSpace H'
 R] [ContMDiffRing I' n R] {U V : Opens N} (h : U <= V) : C^n⟮I, V; I', R⟯ ->+* 
C^n⟮I, U; I', R⟯
参数：R : Type*；h : U <= V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a "`C^n` ring" `R` and open sets `U ⊆ V` in `N`, the "restriction" ring homo
morphism from
`C^n⟮I, V; I', R⟯` to `C^n⟮I, U; I', R⟯`.
-/
def restrictRingHom (R : Type*) [Ring R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] {U V : Opens N} (h : U ≤ V) :
    C^n⟮I, V; I', R⟯ →+* C^n⟮I, U; I', R⟯ :=
  { ContMDiffMap.restrictMonoidHom I I' R h, ContMDiffMap.restrictAddMonoidHom I I' R h with
    toFun := fun f => ⟨f ∘ Set.inclusion h, f.contMDiff.comp (contMDiff_inclusion h)⟩ }

variable {I I'}

/-- Coercion to a function as a `RingHom`. -/
@[simps]
/-
**ContMDiffMap.coeFnRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：coeFnRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H
' R] [ContMDiffRing I' n R] : C^n⟮I, N; I', R⟯ ->+* N -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as a `RingHom`.
-/
def coeFnRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] : C^n⟮I, N; I', R⟯ →+* N → R :=
  { (coeFnMonoidHom : C^n⟮I, N; I', R⟯ →* _), (coeFnAddMonoidHom : C^n⟮I, N; I', R⟯ →+ _) with
    toFun := (↑) }

/-- `Function.eval` as a `RingHom` on the ring of `C^n` functions. -/
/-
**ContMDiffMap.evalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：evalRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H'
 R] [ContMDiffRing I' n R] (m : N) : C^n⟮I, N; I', R⟯ ->+* R
参数：m : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.eval` as a `RingHom` on the ring of `C^n` functions.
-/
def evalRingHom {R : Type*} [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [ContMDiffRing I' n R] (m : N) : C^n⟮I, N; I', R⟯ →+* R :=
  (Pi.evalRingHom _ m : (N → R) →+* R).comp ContMDiffMap.coeFnRingHom

end RingStructure

section ModuleStructure

/-!
### Semimodule structure

In this section we show that `C^n` functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/


/-
**ContMDiffMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：instSMul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] : SMul 𝕜 C^n
⟮I, N; 𝓘(𝕜, V), V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Semimodule structure

In this section we show that `C^n` functions valued in a vector space `M` over a
 normed
field `𝕜` inherit a vector space structure.
-/
instance instSMul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul 𝕜 C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun r f ↦ ⟨r • ⇑f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩⟩

@[simp]
/-
**ContMDiffMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：coe_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜) (f :
 C^n⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f
参数：r : 𝕜；f : C^n⟮I, N; 𝓘(𝕜, V), V⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (f : C^n⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/-
**ContMDiffMap.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：smul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜) (g 
: C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.co
mp h
参数：r : 𝕜；g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯；h : C^n⟮I, N; I'', N'⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (r : 𝕜)
    (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) : (r • g).comp h = r • g.comp h :=
  rfl
/-
**ContMDiffMap.module** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：module {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] : Module 𝕜 C^n
⟮I, N; 𝓘(𝕜, V), V⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.coe_smul`：coe_smul {V : Type*} [NormedAddCommGroup V] [Norm
edSpace 𝕜 V] (r : 𝕜) (f : C^n⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f
-/
instance module {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module 𝕜 C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  Function.Injective.module 𝕜 coeFnAddMonoidHom ContMDiffMap.coe_injective coe_smul

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
/-
**ContMDiffMap.coeFnLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：coeFnLinearMap {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] : C^n⟮
I, N; 𝓘(𝕜, V), V⟯ ->ₗ[𝕜] N -> V
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.coe_smul`：coe_smul {V : Type*} [NormedAddCommGroup V] [Norm
edSpace 𝕜 V] (r : 𝕜) (f : C^n⟮I, N; 𝓘(𝕜, V), V⟯) : ⇑(r • f) = r • ⇑f

--- 原说明 ---
Coercion to a function as a `LinearMap`.
-/
def coeFnLinearMap {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    C^n⟮I, N; 𝓘(𝕜, V), V⟯ →ₗ[𝕜] N → V :=
  { (coeFnAddMonoidHom : C^n⟮I, N; 𝓘(𝕜, V), V⟯ →+ _) with
    toFun := (↑)
    map_smul' := coe_smul }

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that `C^n` functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/


variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [ContMDiffRing 𝓘(𝕜, A) n A]

/-- `C^n` constant functions as a `RingHom`. -/
/-
**ContMDiffMap.C** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：C : 𝕜 ->+* C^n⟮I, N; 𝓘(𝕜, A), A⟯ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C^n` constant functions as a `RingHom`.
-/
def C : 𝕜 →+* C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  toFun := fun c : 𝕜 => ⟨fun _ => (algebraMap 𝕜 A) c, contMDiff_const⟩
  map_one' := by ext; exact (algebraMap 𝕜 A).map_one
  map_mul' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_mul _ _
  map_zero' := by ext; exact (algebraMap 𝕜 A).map_zero
  map_add' c₁ c₂ := by ext; exact (algebraMap 𝕜 A).map_add _ _
/-
**ContMDiffMap.algebra** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：algebra : Algebra 𝕜 C^n⟮I, N; 𝓘(𝕜, A), A⟯ where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra 𝕜 C^n⟮I, N; 𝓘(𝕜, A), A⟯ where
  smul := fun r f ↦ ⟨r • f, contMDiff_const.smul (I := 𝓘(𝕜)) f.contMDiff⟩
  algebraMap := ContMDiffMap.C
  commutes' := fun c f => by ext x; exact Algebra.commutes' _ _
  smul_def' := fun c f => by ext x; exact Algebra.smul_def' _ _

/-- Coercion to a function as an `AlgHom`. -/
@[simps]
/-
**ContMDiffMap.coeFnAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `ContMDiffMap`。
形式化陈述：coeFnAlgHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ ->ₐ[𝕜] N -> A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as an `AlgHom`.
-/
def coeFnAlgHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →ₐ[𝕜] N → A where
  toFun := (↑)
  commutes' _ := rfl
  -- `(ContMDiffMap.coeFnRingHom : C^n⟮I, N; 𝓘(𝕜, A), A⟯ →+* _) with` times out for some reason
  map_zero' := ContMDiffMap.coe_zero
  map_one' := ContMDiffMap.coe_one
  map_add' := ContMDiffMap.coe_add
  map_mul' := ContMDiffMap.coe_mul

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of `C^n` functions from `N` to `V`
is naturally a vector space over the ring of `C^n` functions from `N` to `𝕜`. -/

/-- `C^n` scalar-valued functions act by left-multiplication on `C^n` functions. -/
/-
**ContMDiffMap.instSMul'** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：instSMul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] : SMul C^n⟮
I, N; 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C^n` scalar-valued functions act by left-multiplication on `C^n` functions.
-/
instance instSMul' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    SMul C^n⟮I, N; 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ :=
  ⟨fun f g => ⟨fun x => f x • g x, ContMDiff.smul f.2 g.2⟩⟩

/-- The left multiplication with a `C^n` scalar function commutes with composition. -/
@[simp]
/-
**ContMDiffMap.smul_comp'** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMap`。
形式化陈述：smul_comp' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f : C^n⟮I
'', N'; 𝕜⟯) (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) : (f • g).co
mp h = f.comp h • g.comp h
参数：f : C^n⟮I'', N'; 𝕜⟯；g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯；h : C^n⟮I, N; I'', N'⟯。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left multiplication with a `C^n` scalar function commutes with composition.
-/
theorem smul_comp' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] (f : C^n⟮I'', N'; 𝕜⟯)
    (g : C^n⟮I'', N'; 𝓘(𝕜, V), V⟯) (h : C^n⟮I, N; I'', N'⟯) :
    (f • g).comp h = f.comp h • g.comp h :=
  rfl

/-- The space of `C^n` functions with values in a space `V` is a module over the space of `C^n`
functions with values in `𝕜`. -/
/-
**ContMDiffMap.module'** 是 Mathlib 中的一个实例，位于命名空间 `ContMDiffMap`。
形式化陈述：module' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] : Module C^n⟮
I, N; 𝓘(𝕜), 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ where smul_add c f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜

--- 原说明 ---
The space of `C^n` functions with values in a space `V` is a module over the spa
ce of `C^n`
functions with values in `𝕜`.
-/
instance module' {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] :
    Module C^n⟮I, N; 𝓘(𝕜), 𝕜⟯ C^n⟮I, N; 𝓘(𝕜, V), V⟯ where
  smul_add c f g := by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul 𝕜 (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; exact smul_zero _

end ModuleOverContinuousFunctions

end ContMDiffMap

