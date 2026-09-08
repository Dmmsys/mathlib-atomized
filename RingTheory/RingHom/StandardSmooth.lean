/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Tactic.Algebraize

/-!
# Standard smooth ring homomorphisms

In this file we define standard smooth ring homomorphisms and show their
meta properties.

## Main definitions

- `RingHom.IsStandardSmooth`: A ring homomorphism `R →+* S` is standard smooth if `S` is standard
  smooth as `R`-algebra.
- `RingHom.IsStandardSmoothOfRelativeDimension n`: A ring homomorphism `R →+* S` is standard
  smooth of relative dimension `n` if `S` is standard smooth of relative dimension `n` as
  `R`-algebra.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section
universe t t' w w' u v

variable (n m : ℕ)

open TensorProduct

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism `R →+* S` is standard smooth if `S` is standard smooth as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmooth.toAlgebra]
/-
**RingHom.IsStandardSmooth** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：IsStandardSmooth (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* S` is standard smooth if `S` is standard smooth as `R
`-algebra.
-/
def IsStandardSmooth (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmooth _ _ _ _ f.toAlgebra
/-
**RingHom.isStandardSmooth_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmooth_algebraMap [Algebra R S] : (algebraMap R S).IsStandardSmo
oth ↔ Algebra.IsStandardSmooth R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.IsStandardSmooth.eq_1`：∀ {R : Type u} {S : Type v} [inst : CommR
ing R] [inst_1 : CommRing S] (f : R →+* S),   f.IsStandardSmooth = Algebra.IsSta
ndardSmooth R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isStandardSmooth_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardSmooth ↔ Algebra.IsStandardSmooth R S := by
  rw [RingHom.IsStandardSmooth, toAlgebra_algebraMap]

/-- Helper lemma for the `algebraize` tactic -/
/-
**RingHom.IsStandardSmooth.toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStanda
rdSmooth`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f :
 R →+* S},   f.IsStandardSmooth → Algebra.IsStandardSmooth R S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for the `algebraize` tactic
-/
lemma IsStandardSmooth.toAlgebra {f : R →+* S} (hf : IsStandardSmooth f) :
    @Algebra.IsStandardSmooth R S _ _ f.toAlgebra := hf

/-- A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra]
/-
**RingHom.IsStandardSmoothOfRelativeDimension** 是 Mathlib 中的一个定义，位于命名空间 `RingHom
`。
形式化陈述：IsStandardSmoothOfRelativeDimension (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra.
-/
def IsStandardSmoothOfRelativeDimension (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension n _ _ _ _ f.toAlgebra
/-
**RingHom.isStandardSmoothOfRelativeDimension_algebraMap** 是 Mathlib 中的一个引理，位于命名
空间 `RingHom`。
形式化陈述：isStandardSmoothOfRelativeDimension_algebraMap [Algebra R S] : (algebraMap
 R S).IsStandardSmoothOfRelativeDimension n ↔ Algebra.IsStandardSmoothOfRelative
Dimension n R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.eq_1`：∀ (n : ℕ) {R : Type u}
 {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S),   RingHom
.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isStandardSmoothOfRelativeDimension_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardSmoothOfRelativeDimension n ↔
      Algebra.IsStandardSmoothOfRelativeDimension n R S := by
  rw [RingHom.IsStandardSmoothOfRelativeDimension, toAlgebra_algebraMap]

/-- Helper lemma for the `algebraize` tactic -/
/-
**RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra** 是 Mathlib 中的一个定理，位于命名空
间 `RingHom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (n : ℕ) {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing
 S] {f : R →+* S},   RingHom.IsStandardSmoothOfRelativeDimension n f → Algebra.I
sStandardSmoothOfRelativeDimension n R S
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for the `algebraize` tactic
-/
lemma IsStandardSmoothOfRelativeDimension.toAlgebra {f : R →+* S}
    (hf : IsStandardSmoothOfRelativeDimension n f) :
    @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ f.toAlgebra := hf
/-
**RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth** 是 Mathlib 中的一个定
理，位于命名空间 `RingHom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (n : ℕ) {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing
 S] (f : R →+* S),   RingHom.IsStandardSmoothOfRelativeDimension n f → f.IsStand
ardSmooth
参数：n : ℕ；f : R →+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth`：∀ (n : ℕ) 
{R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S]   [H : Algebra.IsStandardSmoothOfRelati…
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra`：∀ (n : ℕ) {R : Ty
pe u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   Ri
ngHom.IsStandardSmoothOfRelativeDimension n…
-/
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth (f : R →+* S)
    (hf : IsStandardSmoothOfRelativeDimension n f) :
    IsStandardSmooth f := by
  algebraize [f]
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

variable {n m}

variable (R) in
/-
**RingHom.IsStandardSmoothOfRelativeDimension.id** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Hom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ (R : Type u) [inst : CommRing R], RingHom.IsStandardSmoothOfRelativeDime
nsion 0 (RingHom.id R)
参数：R : Type u；RingHom.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.id`：∀ (R : Type u) [inst : C
ommRing R], Algebra.IsStandardSmoothOfRelativeDimension 0 R R
-/
lemma IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension 0 (RingHom.id R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.id R
/-
**RingHom.IsStandardSmoothOfRelativeDimension.equiv** 是 Mathlib 中的一个定理，位于命名空间 `R
ingHom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (e :
 R ≃+* S),   RingHom.IsStandardSmoothOfRelativeDimension 0 ↑e
参数：e : R ≃+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective`：∀ {
R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S],   Function.Bijective ⇑(algebraMap R S) → Algeb…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma IsStandardSmoothOfRelativeDimension.equiv (e : R ≃+* S) :
    IsStandardSmoothOfRelativeDimension 0 (e : R →+* S) := by
  algebraize [e.toRingHom]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

variable {T : Type*} [CommRing T]
/-
**RingHom.IsStandardSmooth.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStandardSmo
oth`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {T :
 Type u_1} [inst_2 : CommRing T] {g : S →+* T}   {f : R →+* S}, g.IsStandardSmoo
th → f.IsStandardSmooth → (g.comp f).IsStandardSmooth
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.IsStandardSmooth.eq_1`：∀ {R : Type u} {S : Type v} [inst : CommR
ing R] [inst_1 : CommRing S] (f : R →+* S),   f.IsStandardSmooth = Algebra.IsSta
ndardSmooth R S
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.IsStandardSmooth.trans`：∀ (R : Type u) (S : Type v) [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (T : Type u_1)   [inst_3 : 
CommRing T] [inst_4 …
· 使用定理 `RingHom.IsStandardSmooth.toAlgebra`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.IsStandardSmooth → Algebra.
IsStandardSmooth R S
-/
lemma IsStandardSmooth.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmooth g) (hf : IsStandardSmooth f) :
    IsStandardSmooth (g.comp f) := by
  rw [IsStandardSmooth]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmooth.trans R S T
/-
**RingHom.IsStandardSmoothOfRelativeDimension.comp** 是 Mathlib 中的一个定理，位于命名空间 `Ri
ngHom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {n m : ℕ} {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRi
ng S] {T : Type u_1} [inst_2 : CommRing T]   {g : S →+* T} {f : R →+* S},   Ring
Hom.IsStandardSmoothOfRelativeDimension n g →     RingHom.IsStandardSmoothOfRela
tiveDimension m f → RingHom.IsStandardSmoothOfRelativeDimension (n + m) (g.comp 
f)
参数：n + m；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.eq_1`：∀ (n : ℕ) {R : Type u}
 {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S),   RingHom
.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.trans`：∀ (n m : ℕ) (R : Type
 u) (S : Type v) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S
] (T : Type u_1)   [inst_3 : CommRing T…
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra`：∀ (n : ℕ) {R : Ty
pe u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   Ri
ngHom.IsStandardSmoothOfRelativeDimension n…
-/
lemma IsStandardSmoothOfRelativeDimension.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmoothOfRelativeDimension n g)
    (hf : IsStandardSmoothOfRelativeDimension m f) :
    IsStandardSmoothOfRelativeDimension (n + m) (g.comp f) := by
  rw [IsStandardSmoothOfRelativeDimension]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans m n R S T
/-
**RingHom.isStandardSmooth_stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `Rin
gHom`。
形式化陈述：isStandardSmooth_stableUnderComposition : StableUnderComposition @IsStanda
rdSmooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardSmooth.comp`：∀ {R : Type u} {S : Type v} [inst : CommR
ing R] [inst_1 : CommRing S] {T : Type u_1} [inst_2 : CommRing T] {g : S →+* T} 
  {f : R →+* S}, g.…
-/
lemma isStandardSmooth_stableUnderComposition :
    StableUnderComposition @IsStandardSmooth :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf
/-
**RingHom.isStandardSmooth_respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmooth_respectsIso : RespectsIso @IsStandardSmooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用引理 `RingHom.isStandardSmooth_stableUnderComposition`：isStandardSmooth_stable
UnderComposition : StableUnderComposition @IsStandardSmooth
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth`：∀ (n : ℕ) 
{R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S
),   RingHom.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.equiv`：∀ {R : Type u} {S : T
ype v} [inst : CommRing R] [inst_1 : CommRing S] (e : R ≃+* S),   RingHom.IsStan
dardSmoothOfRelativeDimension 0 ↑e
-/
lemma isStandardSmooth_respectsIso : RespectsIso @IsStandardSmooth := by
  apply isStandardSmooth_stableUnderComposition.respectsIso
  introv
  exact (IsStandardSmoothOfRelativeDimension.equiv e).isStandardSmooth
/-
**RingHom.isStandardSmoothOfRelativeDimension_respectsIso** 是 Mathlib 中的一个引理，位于命
名空间 `RingHom`。
形式化陈述：isStandardSmoothOfRelativeDimension_respectsIso : RespectsIso (@IsStandard
SmoothOfRelativeDimension n) where left {R S T _ _ _} f e hf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.comp`：∀ {n m : ℕ} {R : Type 
u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {T : Type u_1} [inst_2
 : CommRing T]   {g : S →+* T} {f : R …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.equiv`：∀ {R : Type u} {S : T
ype v} [inst : CommRing R] [inst_1 : CommRing S] (e : R ≃+* S),   RingHom.IsStan
dardSmoothOfRelativeDimension 0 ↑e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma isStandardSmoothOfRelativeDimension_respectsIso :
    RespectsIso (@IsStandardSmoothOfRelativeDimension n) where
  left {R S T _ _ _} f e hf := by
    rw [← zero_add n]
    exact (IsStandardSmoothOfRelativeDimension.equiv e).comp hf
  right {R S T _ _ _} f e hf := by
    rw [← add_zero n]
    exact hf.comp (IsStandardSmoothOfRelativeDimension.equiv e)
/-
**RingHom.isStandardSmooth_isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `Ri
ngHom`。
形式化陈述：isStandardSmooth_isStableUnderBaseChange : IsStableUnderBaseChange @IsStan
dardSmooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.isStandardSmooth_respectsIso`：isStandardSmooth_respectsIso : Res
pectsIso @IsStandardSmooth
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.Algebra.ext`：∀ {S : Type u} {A : Type v} [inst : CommSemir
ing S] [inst_1 : Semiring A] (h1 h2 : Algebra S A),   (∀ (r : S) (x : A),       
(have I := h1; …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `RingHom.IsStandardSmooth.eq_1`：∀ {R : Type u} {S : Type v} [inst : CommR
ing R] [inst_1 : CommRing S] (f : R →+* S),   f.IsStandardSmooth = Algebra.IsSta
ndardSmooth R S
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardSmooth.baseChange`：∀ {R : Type u} {S : Type v} [inst :
 CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (T : Type u_1)   [inst
_3 : CommRing T] [inst_4 …
-/
lemma isStandardSmooth_isStableUnderBaseChange :
    IsStableUnderBaseChange @IsStandardSmooth := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmooth]; convert! this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

variable (n)
/-
**RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange** 是 Mathli
b 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmoothOfRelativeDimension_isStableUnderBaseChange : IsStableUnde
rBaseChange (@IsStandardSmoothOfRelativeDimension n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.isStandardSmoothOfRelativeDimension_respectsIso`：isStandardSmoot
hOfRelativeDimension_respectsIso : RespectsIso (@IsStandardSmoothOfRelativeDimen
sion n) where left {R S T _ _ _} f e hf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.Algebra.ext`：∀ {S : Type u} {A : Type v} [inst : CommSemir
ing S] [inst_1 : Semiring A] (h1 h2 : Algebra S A),   (∀ (r : S) (x : A),       
(have I := h1; …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.eq_1`：∀ (n : ℕ) {R : Type u}
 {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S),   RingHom
.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.baseChange`：∀ (n : ℕ) {R : T
ype u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra 
R S] (T : Type u_1)   [inst_3 : CommRing T] …
-/
lemma isStandardSmoothOfRelativeDimension_isStableUnderBaseChange :
    IsStableUnderBaseChange (@IsStandardSmoothOfRelativeDimension n) := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert! h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmoothOfRelativeDimension n S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmoothOfRelativeDimension]
      convert! this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance
/-
**RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway** 是 
Mathlib 中的一个定理，位于命名空间 `RingHom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {Rᵣ : Type u_2} [inst_1 : CommRing Rᵣ] 
[inst_2 : Algebra R Rᵣ] (r : R)   [IsLocalization.Away r Rᵣ], RingHom.IsStandard
SmoothOfRelativeDimension 0 (algebraMap R Rᵣ)
参数：r : R；algebraMap R Rᵣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.Algebra.ext`：∀ {S : Type u} {A : Type v} [inst : CommSemir
ing S] [inst_1 : Semiring A] (h1 h2 : Algebra S A),   (∀ (r : S) (x : A),       
(have I := h1; …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.eq_1`：∀ (n : ℕ) {R : Type u}
 {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S),   RingHom
.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.localization_away`：∀ {R : Ty
pe u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R
 S] (r : R)   [IsLocalization.Away r S], Algebra.Is…
-/
lemma IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway {Rᵣ : Type*} [CommRing Rᵣ]
    [Algebra R Rᵣ] (r : R) [IsLocalization.Away r Rᵣ] :
    IsStandardSmoothOfRelativeDimension 0 (algebraMap R Rᵣ) := by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension, this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r
/-
**RingHom.isStandardSmooth_localizationPreserves** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom`。
形式化陈述：isStandardSmooth_localizationPreserves : LocalizationPreserves IsStandardS
mooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.isStandardSmooth_isStableUnderBaseChange`：isStandardSmooth_isSta
bleUnderBaseChange : IsStableUnderBaseChange @IsStandardSmooth
-/
lemma isStandardSmooth_localizationPreserves : LocalizationPreserves IsStandardSmooth :=
  isStandardSmooth_isStableUnderBaseChange.localizationPreserves
/-
**RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves** 是 Mathlib 
中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmoothOfRelativeDimension_localizationPreserves : LocalizationPr
eserves (IsStandardSmoothOfRelativeDimension n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange`：isS
tandardSmoothOfRelativeDimension_isStableUnderBaseChange : IsStableUnderBaseChan
ge (@IsStandardSmoothOfRelativeDimension n)
-/
lemma isStandardSmoothOfRelativeDimension_localizationPreserves :
    LocalizationPreserves (IsStandardSmoothOfRelativeDimension n) :=
  (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves
/-
**RingHom.isStandardSmooth_holdsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 `R
ingHom`。
形式化陈述：isStandardSmooth_holdsForLocalizationAway : HoldsForLocalizationAway IsSta
ndardSmooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth`：∀ (n : ℕ) 
{R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S
),   RingHom.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAwa
y`：∀ {R : Type u} [inst : CommRing R] {Rᵣ : Type u_2} [inst_1 : CommRing Rᵣ] [in
st_2 : Algebra R Rᵣ] (r : R)   [IsLocalization.Away r Rᵣ], Ring…
-/
lemma isStandardSmooth_holdsForLocalizationAway :
    HoldsForLocalizationAway IsStandardSmooth := by
  introv R h
  exact (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r).isStandardSmooth
/-
**RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway** 是 Mathl
ib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmoothOfRelativeDimension_holdsForLocalizationAway : HoldsForLoc
alizationAway (IsStandardSmoothOfRelativeDimension 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAwa
y`：∀ {R : Type u} [inst : CommRing R] {Rᵣ : Type u_2} [inst_1 : CommRing Rᵣ] [in
st_2 : Algebra R Rᵣ] (r : R)   [IsLocalization.Away r Rᵣ], Ring…
-/
lemma isStandardSmoothOfRelativeDimension_holdsForLocalizationAway :
    HoldsForLocalizationAway (IsStandardSmoothOfRelativeDimension 0) := by
  introv R h
  exact IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
/-
**RingHom.isStandardSmooth_stableUnderCompositionWithLocalizationAway** 是 Mathli
b 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmooth_stableUnderCompositionWithLocalizationAway : StableUnderC
ompositionWithLocalizationAway IsStandardSmooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用引理 `RingHom.isStandardSmooth_stableUnderComposition`：isStandardSmooth_stable
UnderComposition : StableUnderComposition @IsStandardSmooth
· 使用引理 `RingHom.isStandardSmooth_holdsForLocalizationAway`：isStandardSmooth_hold
sForLocalizationAway : HoldsForLocalizationAway IsStandardSmooth
-/
lemma isStandardSmooth_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway IsStandardSmooth :=
  isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    isStandardSmooth_holdsForLocalizationAway
/-
**RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocaliza
tionAway** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalization
Away : StableUnderCompositionWithLocalizationAway (IsStandardSmoothOfRelativeDim
ension n) where left R S _ _ _ _ _ r _ _ hf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAwa
y`：∀ {R : Type u} [inst : CommRing R] {Rᵣ : Type u_2} [inst_1 : CommRing Rᵣ] [in
st_2 : Algebra R Rᵣ] (r : R)   [IsLocalization.Away r Rᵣ], Ring…
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.comp`：∀ {n m : ℕ} {R : Type 
u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {T : Type u_1} [inst_2
 : CommRing T]   {g : S →+* T} {f : R …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway (IsStandardSmoothOfRelativeDimension n) where
  left R S _ _ _ _ _ r _ _ hf :=
    have : (algebraMap R S).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
    add_zero n ▸ IsStandardSmoothOfRelativeDimension.comp hf this
  right _ S T _ _ _ _ s _ _ hf :=
    have : (algebraMap S T).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway s
    zero_add n ▸ IsStandardSmoothOfRelativeDimension.comp this hf

set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/-- Every standard smooth homomorphism `R → S` factors into `R -> R[X₁,...,Xₙ] → S`
where `n` is the relative dimension and `R[X₁,...,Xₙ] → S` is etale. -/
/-
**RingHom._root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPoly
nomial** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every standard smooth homomorphism `R → S` factors into `R -> R[X₁,...,Xₙ] → S`
where `n` is the relative dimension and `R[X₁,...,Xₙ] → S` is etale.
-/
theorem _root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ g : MvPolynomial (Fin n) R →ₐ[R] S, g.Etale := by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := S) (n := n)
  let e₀ : σ ⊕ Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl,
        Set.ncard_range_of_injective P.map_inj, ← e, Algebra.Presentation.dimension])).symm).trans
      (Equiv.Set.sumCompl _)
  let e : MvPolynomial σ (MvPolynomial (Fin n) R) ≃ₐ[R] P.Ring :=
    (MvPolynomial.sumAlgEquiv R _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom _ (MvPolynomial (Fin n) R) _)
  algebraize [φ.toRingHom, (algebraMap P.Ring S).comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower R (MvPolynomial (Fin n) R) S := .to₁₂₄ _ _ P.Ring _
  refine ⟨IsScalarTower.toAlgHom _ _ _, ?_⟩
  have H : (MvPolynomial.aeval fun x ↦ (algebraMap P.Ring S) (e (MvPolynomial.X x))).toRingHom =
      (algebraMap P.Ring S).comp e.toRingHom := by
    ext
    · simp [e, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) S]
    · simp [e, @RingHom.algebraMap_toAlgebra (MvPolynomial (Fin n) R) S, φ]
    · simp [e]
  let P' : Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { toGenerators := .ofSurjective (algebraMap _ _ <| e <| .X ·) <| by
      convert! P.algebraMap_surjective.comp e.surjective
      exact congr($H)
    relation := e.symm ∘ P.relation
    span_range_relation_eq_ker := by
      rw [Set.range_comp, ← AlgEquiv.coe_ringEquiv e.symm, AlgEquiv.symm_toRingEquiv,
        ← Ideal.map_span, P.span_range_relation_eq_ker, Ideal.map_symm]
      exact congr(RingHom.ker $H).symm
    map := _
    map_inj := Function.injective_id }
  let P' : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { __ := P'
    jacobian_isUnit := by
      convert! P.jacobian_isUnit using 1
      simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
      congr 1
      ext i j
      trans algebraMap P.Ring S (e ((e.symm (P.relation j)).pderiv i))
      · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
          Algebra.Generators.ofSurjective] using congr($H _)
      suffices e ((e.symm (P.relation j)).pderiv i) = (P.relation j).pderiv (P.map i) by
        simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
      simp [e, ← MvPolynomial.pderiv_rename e₀.injective, show e₀ (Sum.inl i) = P.map i from rfl] }
  exact etale_algebraMap.mpr (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨_, _, _, inferInstance, P', by simp [Algebra.Presentation.dimension]⟩)

/-- Every standard smooth homomorphism `R → S` factors into `R -> R[X₁,...,Xₙ] → S`
where `n` is the relative dimension and `R[X₁,...,Xₙ] → S` is etale. -/
/-
**RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial** 是 Math
lib 中的一个定理，位于命名空间 `RingHom.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f :
 R →+* S} {n : ℕ},   RingHom.IsStandardSmoothOfRelativeDimension n f → ∃ g, g.co
mp MvPolynomial.C = f ∧ g.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`：∀
 (n : ℕ) (R : Type u) (S : Type v) [inst : CommRing R] [inst_1 : CommRing S] [in
st_2 : Algebra R S]   [Algebra.IsStandardSmoothOfRelativeDi…
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra`：∀ (n : ℕ) {R : Ty
pe u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   Ri
ngHom.IsStandardSmoothOfRelativeDimension n…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B

--- 原说明 ---
Every standard smooth homomorphism `R → S` factors into `R -> R[X₁,...,Xₙ] → S`
where `n` is the relative dimension and `R[X₁,...,Xₙ] → S` is etale.
-/
theorem IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    {f : R →+* S} {n : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension n) :
    ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  algebraize [f]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  exact ⟨_, g.comp_algebraMap, hg⟩
/-
**RingHom.IsStandardSmooth.exists_etale_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `
RingHom.IsStandardSmooth`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f :
 R →+* S},   f.IsStandardSmooth → ∃ n g, g.comp MvPolynomial.C = f ∧ g.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`：∀
 {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* 
S} {n : ℕ},   RingHom.IsStandardSmoothOfRelativeDimension n…
-/
theorem IsStandardSmooth.exists_etale_mvPolynomial
    {f : R →+* S} (hf : f.IsStandardSmooth) :
    ∃ n, ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

end RingHom

