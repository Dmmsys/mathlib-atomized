/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Pepa Montero
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Cⁿ monoid actions

In this file we define Cⁿ actions (e.g. by Lie groups or monoids) on manifolds: we say
`ContMDiffSMul I I' n G M` if `G` acts multiplicatively on `M` and the action map
`fun p : G × M ↦ p.1 • p.2` is Cⁿ. We also provide API for additive actions using `@[to_additive]`.

We also provide `ContMDiffSMul` instances for scalar multiplication in normed spaces and for
the action of the monoid `E →L[𝕜] E` of continuous linear maps on any normed space `E`.

For a group `G` acting smoothly on `M`, we define `Diffeomorph.smul`, scalar multiplication by a
fixed `g : G` as a diffeomorphism of `M` (in analogy to `Homeomorph.smul`).

See also:
* `ContMDiffMul I n G` for continuous differentiability of multiplication `G × G → G` in a single
  type `G`,
* `ContinuousSMul G M` for continuity of an action `G × M → M`.

Unlike for continuous actions, we do not currently have a class `ContMDiffConstSMul`. If there are
interesting examples satisfying `ContMDiffConstSMul` but not `ContMDiffSMul`, this can be added
later. (Note that such examples may be harder to find: in fact, a continuous action of a
Lie group `G` on a finite-dimensional manifold `M` is `C^n` provided it is `C^n` in the
second variable.)
-/

open scoped Manifold ContDiff

public section

/-- Basic typeclass stating that the additive action of `G` on `M` is Cⁿ as a function `G × M → M`.
Unlike with `ContMDiffAdd` (the class stating that addition `G × G → G` within a single type `G` is
Cⁿ), we do not extend `IsManifold` because `ContMDiffVAdd` contains more
explicit arguments than `IsManifold` and so `ContMDiffVAdd.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffVAdd` to be meaningful, smoothness of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ additive Lie group with a Cⁿ
additive action on a Cⁿ manifold `M`, one can use the typeclasses
`[LieAddGroup I n G] [IsManifold I' n M] [ContMDiffVAdd I I' n G M]`. -/
/-
**ContMDiffVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     ModelWithCorners 𝕜 E H →                 {H' : Type u_4} →                 
  [inst_4 : TopologicalSpace H'] →                     {E' : Type u_5} →        
               [inst_5 : NormedAddCommGroup E'] →                         [inst_
6 : NormedSpace 𝕜 E'] →                           ModelWithCorners 𝕜 E' H' →    
                         WithTop ℕ∞ →                               (G : Type u_
6) →                                 [inst : TopologicalSpace G] →              
                     [ChartedSpace H G] →                                     (M
 : Type u_7) →                                       [inst : TopologicalSpace M]
 → [ChartedSpace H' M] → [VAdd G M] → Prop
参数：G : Type u_6；M : Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic typeclass stating that the additive action of `G` on `M` is Cⁿ as a functi
on `G × M → M`.
Unlike with `ContMDiffAdd` (the class stating that addition `G × G → G` within a
 single type `G` is
Cⁿ), we do not extend `IsManifold` because `ContMDiffVAdd` contains more
explicit arguments than `IsManifold` and so `ContMDiffVAdd.toIsManifold` could n
ot be an instance
anyway: this means that in order for `ContMDiffVAdd` to be meaningful, smoothnes
s of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ additive 
Lie group with a Cⁿ
additive action on a Cⁿ manifold `M`, one can use the typeclasses
`[LieAddGroup I n G] [IsManifold I' n M] [ContMDiffVAdd I I' n G M]`.
-/
class ContMDiffVAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [VAdd G M] : Prop where
  contMDiff_vadd : CMDiff n fun p : G × M ↦ p.1 +ᵥ p.2

/-- Basic typeclass stating that the action of `G` on `M` is Cⁿ as a function `G × M → M`.
Unlike with `ContMDiffMul` (the class stating that multiplication `G × G → G` within a single type
`G` is Cⁿ), we do not extend `IsManifold` because `ContMDiffSMul` contains more
explicit arguments than `IsManifold` and so `ContMDiffSMul.toIsManifold` could not be an instance
anyway: this means that in order for `ContMDiffSMul` to be meaningful, smoothness of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ Lie group with a Cⁿ action on
a Cⁿ manifold `M`, one can use the typeclasses
`[LieGroup I n G] [IsManifold I' n M] [ContMDiffSMul I I' n G M]`. -/
@[to_additive]
/-
**ContMDiffSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     ModelWithCorners 𝕜 E H →                 {H' : Type u_4} →                 
  [inst_4 : TopologicalSpace H'] →                     {E' : Type u_5} →        
               [inst_5 : NormedAddCommGroup E'] →                         [inst_
6 : NormedSpace 𝕜 E'] →                           ModelWithCorners 𝕜 E' H' →    
                         WithTop ℕ∞ →                               (G : Type u_
6) →                                 [inst : TopologicalSpace G] →              
                     [ChartedSpace H G] →                                     (M
 : Type u_7) →                                       [inst : TopologicalSpace M]
 → [ChartedSpace H' M] → [SMul G M] → Prop
参数：G : Type u_6；M : Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic typeclass stating that the action of `G` on `M` is Cⁿ as a function `G × M
 → M`.
Unlike with `ContMDiffMul` (the class stating that multiplication `G × G → G` wi
thin a single type
`G` is Cⁿ), we do not extend `IsManifold` because `ContMDiffSMul` contains more
explicit arguments than `IsManifold` and so `ContMDiffSMul.toIsManifold` could n
ot be an instance
anyway: this means that in order for `ContMDiffSMul` to be meaningful, smoothnes
s of `G` and `M`
have to be required separately. For example, to state that `G` is a Cⁿ Lie group
 with a Cⁿ action on
a Cⁿ manifold `M`, one can use the typeclasses
`[LieGroup I n G] [IsManifold I' n M] [ContMDiffSMul I I' n G M]`.
-/
class ContMDiffSMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] : Prop where
  contMDiff_smul : CMDiff n fun p : G × M ↦ p.1 • p.2

export ContMDiffVAdd (contMDiff_vadd)

export ContMDiffSMul (contMDiff_smul)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'} {H'' : Type*} [TopologicalSpace H''] {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]

@[to_additive]
/-
**ContMDiffSMul.of_le** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffSMul`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {H' : Type u_4}   [inst_4 : Topo
logicalSpace H'] {E' : Type u_5} [inst_5 : NormedAddCommGroup E'] [inst_6 : Norm
edSpace 𝕜 E']   {I' : ModelWithCorners 𝕜 E' H'} {G : Type u_8} [inst_7 : Topolog
icalSpace G] [inst_8 : ChartedSpace H G]   {M : Type u_9} [inst_9 : TopologicalS
pace M] [inst_10 : ChartedSpace H' M] [inst_11 : SMul G M] {n m : WithTop ℕ∞},  
 n ≤ m → ∀ [ContMDiffSMul I I' m G M], ContMDiffSMul I I' n G M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `ContMDiffSMul.contMDiff_smul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…
-/
protected theorem ContMDiffSMul.of_le [SMul G M] {n m : ℕ∞ω} (h : n ≤ m)
    [ContMDiffSMul I I' m G M] : ContMDiffSMul I I' n G M := ⟨contMDiff_smul.of_le h⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' ∞ G M] [ENat.LEInfty n] :
    ContMDiffSMul I I' n G M :=
  .of_le ENat.LEInfty.out

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' ω G M] : ContMDiffSMul I I' n G M :=
  .of_le le_top

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul G M] [ContinuousSMul G M] : ContMDiffSMul I I' 0 G M :=
  ⟨contMDiff_zero_iff.2 continuous_smul⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul G M] [ContMDiffSMul I I' 2 G M] : ContMDiffSMul I I' 1 G M :=
  .of_le one_le_two

/-- If an action is Cⁿ for some `n`, it is also continuous. This has to be a theorem instead of an
instance because `ContMDiffSMul` depends on parameters `I`, `I'` and `n` that `ContinuousSMul`
doesn't. -/
@[to_additive]
/-
**ContMDiffSMul.continuousSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffSMul.continuousSMul [SMul G M] (n : Nat∞ω) [ContMDiffSMul I I' n 
G M] : ContinuousSMul G M
参数：n : Nat∞ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `ContMDiffSMul.contMDiff_smul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…

--- 原说明 ---
If an action is Cⁿ for some `n`, it is also continuous. This has to be a theorem
 instead of an
instance because `ContMDiffSMul` depends on parameters `I`, `I'` and `n` that `C
ontinuousSMul`
doesn't.
-/
lemma ContMDiffSMul.continuousSMul [SMul G M] (n : ℕ∞ω) [ContMDiffSMul I I' n G M] :
    ContinuousSMul G M :=
  ⟨(contMDiff_smul (I := I) (I' := I') (n := n)).continuous⟩

/-- For any `G` in which multiplication is Cⁿ, the action of `G` on itself via left multiplication
is Cⁿ too. -/
/-
**ContMDiffMul.contMDiffSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContMDiffMul.contMDiffSMul [Mul G] {n : Nat∞ω} [ContMDiffMul I n G] : Cont
MDiffSMul I I n G G where contMDiff_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMul.contMDiff_mul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedF
ield 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : 
NormedAddCommGro…

--- 原说明 ---
For any `G` in which multiplication is Cⁿ, the action of `G` on itself via left 
multiplication
is Cⁿ too.
-/
instance ContMDiffMul.contMDiffSMul [Mul G] {n : ℕ∞ω} [ContMDiffMul I n G] :
    ContMDiffSMul I I n G G where
  contMDiff_smul := contMDiff_mul

section

variable [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
  {f : N → G} {g : N → M} {s : Set N} {x : N}

@[to_additive]
/-
**ContMDiffWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.smul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
 CMDiffAt[s] n (f • g) x
参数：hf : CMDiffAt[s] n f x；hg : CMDiffAt[s] n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `ContMDiffSMul.contMDiff_smul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…
· 使用定理 `ContMDiffWithinAt.prodMk`：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M 
-> N'} (hf : ContMDiffWithinAt I I' n f s x) (hg : ContMDiffWithinAt I J' n g s 
x) : ContMDiff…
-/
theorem ContMDiffWithinAt.smul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
    CMDiffAt[s] n (f • g) x :=
  (contMDiff_smul (I := I) (I' := I')).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.smul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) :
    CMDiffAt n (f • g) x :=
  hf.smul hg

@[to_additive]
/-
**ContMDiffOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.smul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) : CMDiff[s] n (
f • g)
参数：hf : CMDiff[s] n f；hg : CMDiff[s] n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.smul`：ContMDiffWithinAt.smul (hf : CMDiffAt[s] n f x) 
(hg : CMDiffAt[s] n g x) : CMDiffAt[s] n (f • g) x
-/
theorem ContMDiffOn.smul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) :
    CMDiff[s] n (f • g) := fun x hx ↦ (hf x hx).smul (hg x hx)

@[to_additive]
/-
**ContMDiff.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) : CMDiff n (f • g)
参数：hf : CMDiff n f；hg : CMDiff n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H
 : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddC
ommGro…
-/
theorem ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n (f • g) := fun x ↦ (hf x).smul (hg x)

-- TODO: after #41534 is merged, weaken the hypothesis to `ContMDiffConstSMul`
@[to_additive]
/-
**ContMDiffSMul.contMDiff_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffSMul.contMDiff_const_smul {n : Nat∞ω} [ContMDiffSMul I I' n G M] 
(g : G) : CMDiff n fun x : M => g • x
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.smul`：ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) : CMD
iff n (f • g)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
-/
theorem ContMDiffSMul.contMDiff_const_smul {n : ℕ∞ω} [ContMDiffSMul I I' n G M] (g : G) :
    CMDiff n fun x : M ↦ g • x :=
  contMDiff_const.smul (I := I) contMDiff_id

end

@[to_additive prod]
/-
**Prod.contMDiffSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.contMDiffSMul [SMul G M] [SMul G N] {n : Nat∞ω} [ContMDiffSMul I I' n
 G M] [ContMDiffSMul I I'' n G N] : ContMDiffSMul I (I'.prod I'') n G (M × N) wh
ere contMDiff_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContMDiff.smul`：ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) : CMD
iff n (f • g)
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
-/
instance Prod.contMDiffSMul [SMul G M] [SMul G N] {n : ℕ∞ω} [ContMDiffSMul I I' n G M]
    [ContMDiffSMul I I'' n G N] : ContMDiffSMul I (I'.prod I'') n G (M × N) where
  contMDiff_smul := (contMDiff_fst.smul <| contMDiff_fst.comp contMDiff_snd).prodMk <|
      contMDiff_fst.smul <| contMDiff_snd.comp contMDiff_snd

/-- If `G` acts continuously differentiably on `G'` and `G'` acts continuously differentiably on
`M`, then `G` acts continuously differentiably on `M`. -/
/-
**IsScalarTower.contMDiffSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsScalarTower.contMDiffSMul (G' : Type*) [TopologicalSpace G'] [ChartedSpa
ce H'' G'] [Monoid G'] [SMul G G'] [MulAction G' M] [SMul G M] [IsScalarTower G 
G' M] {n : Nat∞ω} [ContMDiffSMul I I'' n G G'] [ContMDiffSMul I'' I' n G' M] : C
ontMDiffSMul I I' n G M where contMDiff_smul
参数：G' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.smul`：ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) : CMD
iff n (f • g)
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
If `G` acts continuously differentiably on `G'` and `G'` acts continuously diffe
rentiably on
`M`, then `G` acts continuously differentiably on `M`.
-/
lemma IsScalarTower.contMDiffSMul (G' : Type*) [TopologicalSpace G'] [ChartedSpace H'' G']
    [Monoid G'] [SMul G G'] [MulAction G' M] [SMul G M] [IsScalarTower G G' M] {n : ℕ∞ω}
    [ContMDiffSMul I I'' n G G'] [ContMDiffSMul I'' I' n G' M] : ContMDiffSMul I I' n G M where
  contMDiff_smul := by
    suffices CMDiff n (fun p : G × M ↦ (p.1 • (1 : G')) • p.2) by simpa
    exact (contMDiff_fst.smul contMDiff_const).smul (I := I'') contMDiff_snd

/-- If an action is continuously differentiable, then post-composing this action with a continuously
differentiable homomorphism gives again a continuously differentiable action. -/
@[to_additive]
/-
**MulAction.contMDiffSMul_compHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.contMDiffSMul_compHom [Monoid G] [MulAction G M] {n : Nat∞ω} [Co
ntMDiffSMul I I' n G M] {G' : Type*} [TopologicalSpace G'] [ChartedSpace H'' G']
 [Monoid G'] {f : G' ->* G} (hf : CMDiff n f) : letI : MulAction G' M
参数：hf : CMDiff n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.smul`：ContMDiff.smul (hf : CMDiff n f) (hg : CMDiff n g) : CMD
iff n (f • g)
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)

--- 原说明 ---
If an action is continuously differentiable, then post-composing this action wit
h a continuously
differentiable homomorphism gives again a continuously differentiable action.
-/
theorem MulAction.contMDiffSMul_compHom [Monoid G] [MulAction G M] {n : ℕ∞ω}
    [ContMDiffSMul I I' n G M] {G' : Type*} [TopologicalSpace G'] [ChartedSpace H'' G'] [Monoid G']
    {f : G' →* G} (hf : CMDiff n f) :
    letI : MulAction G' M := MulAction.compHom _ f
    ContMDiffSMul I'' I' n G' M := by
  let _ : MulAction G' M := MulAction.compHom _ f
  exact ⟨(hf.comp contMDiff_fst).smul contMDiff_snd⟩

/-- The scalar multiplication `𝕜 × E → E` of any normed vector space `E` over `𝕜` is smooth. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplication `𝕜 × E → E` of any normed vector space `E` over `𝕜` is
 smooth.
-/
instance {n : ℕ∞ω} : ContMDiffSMul 𝓘(𝕜) 𝓘(𝕜, E) n 𝕜 E where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(𝕜).prod 𝓘(𝕜, E)) 𝓘(𝕜, 𝕜 × E) n (@id (𝕜 × E)) := by
      rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]; exact contMDiff_id
    exact contDiff_smul.contMDiff.comp h

/-- The monoid `E →L[𝕜] E` of continuous linear endomorphisms of `E` acts smoothly on `E`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid `E →L[𝕜] E` of continuous linear endomorphisms of `E` acts smoothly o
n `E`.
-/
instance {n : ℕ∞ω} : ContMDiffSMul 𝓘(𝕜, E →L[𝕜] E) 𝓘(𝕜, E) n (E →L[𝕜] E) E where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(𝕜, E →L[𝕜] E).prod 𝓘(𝕜, E)) 𝓘(𝕜, (E →L[𝕜] E) × E) n
        (@id ((E →L[𝕜] E) × E)) := by
      rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]; exact contMDiff_id
    exact isBoundedBilinearMap_apply.contDiff.contMDiff.comp h

section Diffeomorph

variable [Group G] [MulAction G M] {n : ℕ∞ω} [ContMDiffSMul I I' n G M] (g : G)

variable (I I' n) in
/-- The diffeomorphism given by scalar multiplication by an element of a group `G` acting
Cⁿ-differentiably on a manifold `M` is a diffeomorphism from `M` to itself. Its inverse is scalar
multiplication by `g⁻¹`. -/
@[expose, to_additive
/-- The diffeomorphism given by affine-addition of an element of an additive group `G` acting
Cⁿ-differentiably on a manifold `M` is a diffeomorphism from `M` to itself. Its inverse is
addition of `-g`. -/]
/-
**Diffeomorph.smul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Diffeomorph.smul : M ≃ₘ^n⟮I', I'⟯ M where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Diffeomorph.smul : M ≃ₘ^n⟮I', I'⟯ M where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := ContMDiffSMul.contMDiff_const_smul (I := I) g
  contMDiff_invFun := ContMDiffSMul.contMDiff_const_smul (I := I) g⁻¹

@[to_additive (attr := simp)]
/-
**Diffeomorph.smul_toHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.smul_toHomeomorph : haveI : ContinuousSMul G M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Diffeomorph.smul_toHomeomorph :
    haveI : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := I') n
    (Diffeomorph.smul I I' n g).toHomeomorph = Homeomorph.smul (α := M) g :=
  rfl

@[to_additive (attr := simp)]
/-
**Diffeomorph.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.smul_apply (x : M) : Diffeomorph.smul I I' n g x = g • x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Diffeomorph.smul_apply (x : M) : Diffeomorph.smul I I' n g x = g • x := rfl

@[to_additive (attr := simp)]
/-
**Diffeomorph.smul_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.smul_symm_apply (x : M) : (Diffeomorph.smul I I' n g).symm x =
 g⁻¹ • x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Diffeomorph.smul_symm_apply (x : M) : (Diffeomorph.smul I I' n g).symm x = g⁻¹ • x := rfl

@[to_additive]
/-
**Diffeomorph.smul_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Diffeomorph.smul_symm : (Diffeomorph.smul I I' n g : M ≃ₘ^n⟮I', I'⟯ M).sym
m = Diffeomorph.smul I I' n g⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeomorph.ext`：ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : forall x, h x = h'
 x) : h = h'
-/
lemma Diffeomorph.smul_symm :
    (Diffeomorph.smul I I' n g : M ≃ₘ^n⟮I', I'⟯ M).symm = Diffeomorph.smul I I' n g⁻¹ :=
  Diffeomorph.ext fun _ ↦ rfl

end Diffeomorph

