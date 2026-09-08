/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.RingTheory.Congruence.Defs

/-!
# Congruence relations on rings

This file contains basic results concerning congruence relations on rings,
which extend `Con` and `AddCon` on monoids and additive monoids.

Most of the time you likely want to use the `Ideal.Quotient` API that is built on top of this.

## Main Definitions

* `RingCon R`: the type of congruence relations respecting `+` and `*`.
* `RingConGen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Copy across more API from `Con` and `AddCon` in `Mathlib/GroupTheory/Congruence/`.
-/

@[expose] public section

variable {α β R R' : Type*}

namespace RingCon

section Quotient

section Algebraic

/-! ### Scalar multiplication

The operation of scalar multiplication `•` descends naturally to the quotient.
-/

section SMul

variable [Add R] [MulOneClass R]
variable [SMul α R] [IsScalarTower α R R]
variable [SMul β R] [IsScalarTower β R R]
variable (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul α c.Quotient := ⟨c.smulAux (Con.smul c.toCon)⟩

@[simp, norm_cast]
/-
**RingCon.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient)
参数：a : α；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (a : α) (x : R) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass α β R] : SMulCommClass α β c.Quotient :=
  inferInstanceAs (SMulCommClass α β c.toCon.Quotient)
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul α β] [IsScalarTower α β R] : IsScalarTower α β c.Quotient :=
  inferInstanceAs (IsScalarTower α β c.toCon.Quotient)
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul αᵐᵒᵖ R] [IsCentralScalar α R] : IsCentralScalar α c.Quotient :=
  inferInstanceAs (IsCentralScalar α c.toCon.Quotient)

end SMul

/-
**RingCon.isScalarTower_right** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
形式化陈述：isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R 
R] (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient where smul_assoc _
参数：c : RingCon R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ : Se
toid β} {p : Quotient s₁ → Quotient s₂ → Prop},   (∀ (a₁ : α) (a₂ : β), p (Quoti
ent.…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
instance isScalarTower_right [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    (c : RingCon R) : IsScalarTower α c.Quotient c.Quotient where
  smul_assoc _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul_assoc _ _ _
/-
**RingCon.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
形式化陈述：smulCommClass [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] [SM
ulCommClass α R R] (c : RingCon R) : SMulCommClass α c.Quotient c.Quotient where
 smul_comm _
参数：c : RingCon R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ : Se
toid β} {p : Quotient s₁ → Quotient s₂ → Prop},   (∀ (a₁ : α) (a₂ : β), p (Quoti
ent.…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
instance smulCommClass [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : RingCon R) : SMulCommClass α c.Quotient c.Quotient where
  smul_comm _ := Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| (mul_smul_comm _ _ _).symm
/-
**RingCon.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
形式化陈述：smulCommClass' [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R] [S
MulCommClass R α R] (c : RingCon R) : SMulCommClass c.Quotient α c.Quotient
参数：c : RingCon R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance smulCommClass' [Add R] [MulOneClass R] [SMul α R] [IsScalarTower α R R]
    [SMulCommClass R α R] (c : RingCon R) : SMulCommClass c.Quotient α c.Quotient :=
  haveI := SMulCommClass.symm R α R
  SMulCommClass.symm _ _ _
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [NonAssocSemiring R] [MulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : MulAction α c.Quotient :=
  inferInstanceAs <| MulAction α c.toCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [NonAssocSemiring R] [DistribMulAction α R] [IsScalarTower α R R]
    (c : RingCon R) : DistribMulAction α c.Quotient where
  smul_zero := fun _ => congr_arg toQuotient <| smul_zero _
  smul_add := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient <| smul_add _ _ _
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [Semiring R] [MulSemiringAction α R] [IsScalarTower α R R] (c : RingCon R) :
    MulSemiringAction α c.Quotient where
  smul_one := fun _ => congr_arg toQuotient <| smul_one _
  smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg toQuotient <|
    MulSemiringAction.smul_mul _ _ _

section
variable [CommSemiring α] [Semiring R] [Algebra α R]

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : RingCon R) : Algebra α c.Quotient where
  algebraMap := c.mk'.comp (algebraMap α R)
  commutes' _ := Quotient.ind' fun _ ↦ congr_arg Quotient.mk'' <| Algebra.commutes _ _
  smul_def' _ := Quotient.ind' fun _ ↦ congr_arg Quotient.mk'' <| Algebra.smul_def _ _

@[simp, norm_cast]
/-
**RingCon.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_algebraMap (c : RingCon R) (s : α) : (algebraMap α R s : c.Quotient) =
 algebraMap α c.Quotient s
参数：c : RingCon R；s : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap (c : RingCon R) (s : α) :
    (algebraMap α R s : c.Quotient) = algebraMap α c.Quotient s :=
  rfl

variable (α) in
/-- The algebra morphism from `R` to the quotient by a ring congruence. -/
/-
**RingCon.mk** 是 Mathlib 中的一个ctor，位于命名空间 `RingCon`。
形式化陈述：{R : Type u_1} →   [inst : Add R] →     [inst_1 : Mul R] →       (toCon : 
Con R) →         (∀ {w x y z : R}, toCon.toSetoid w x → toCon.toSetoid y z → toC
on.toSetoid (w + y) (x + z)) → RingCon R
参数：toCon : Con R；∀ {w x y z : R}, toCon.toSetoid w x → toCon.toSetoid y z → toCo
n.toSetoid (w + y) (x + z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra morphism from `R` to the quotient by a ring congruence.
-/
@[simps!] def mkₐ (c : RingCon R) : R →ₐ[α] c.Quotient :=
  { mk' c with commutes' _ := rfl }
/-
**RingCon.mk** 是 Mathlib 中的一个ctor，位于命名空间 `RingCon`。
形式化陈述：{R : Type u_1} →   [inst : Add R] →     [inst_1 : Mul R] →       (toCon : 
Con R) →         (∀ {w x y z : R}, toCon.toSetoid w x → toCon.toSetoid y z → toC
on.toSetoid (w + y) (x + z)) → RingCon R
参数：toCon : Con R；∀ {w x y z : R}, toCon.toSetoid w x → toCon.toSetoid y z → toCo
n.toSetoid (w + y) (x + z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkₐ_surjective (c : RingCon R) :
    Function.Surjective (c.mkₐ (α := α)) :=
  mk'_surjective c

end

end Algebraic

end Quotient

/-! ### Lattice structure

The API in this section is copied from `Mathlib/GroupTheory/Congruence/Defs.lean`
-/

section Lattice

variable [Add R] [Mul R] [Add R'] [Mul R'] {c d : RingCon R}

/-- For congruence relations `c, d` on a type `M` with multiplication and addition, `c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For congruence relations `c, d` on a type `M` with multiplication and addition, 
`c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`.
-/
instance : LE (RingCon R) where
  le c d := ∀ ⦃x y⦄, c x y → d x y

/-- Definition of `≤` for congruence relations. -/
/-
**RingCon.le_def** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：le_def : c <= d ↔ forall {x y}, c x y -> d x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of `≤` for congruence relations.
-/
theorem le_def : c ≤ d ↔ ∀ {x y}, c x y → d x y := .rfl

@[gcongr]
/-
**RingCon.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_mono {F : Type*} [FunLike F R R'] [AddHomClass F R R'] [MulHomClass 
F R R'] {J J' : RingCon R'} {f : F} (h : J <= J') : J.comap f <= J'.comap f
参数：h : J <= J'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_mono
    {F : Type*} [FunLike F R R'] [AddHomClass F R R'] [MulHomClass F R R']
    {J J' : RingCon R'} {f : F} (h : J ≤ J') :
    J.comap f ≤ J'.comap f :=
  fun _ _ h₁ ↦ h h₁

/-- The infimum of a set of congruence relations on a given type with multiplication and
addition. -/
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of a set of congruence relations on a given type with multiplication
 and
addition.
-/
instance : InfSet (RingCon R) where
  sInf S :=
    { r := fun x y => ∀ c : RingCon R, c ∈ S → c x y
      iseqv :=
        ⟨fun x c _hc => c.refl x, fun h c hc => c.symm <| h c hc, fun h1 h2 c hc =>
          c.trans (h1 c hc) <| h2 c hc⟩
      add' := fun h1 h2 c hc => c.add (h1 c hc) <| h2 c hc
      mul' := fun h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying equivalence relation. -/
/-
**RingCon.sInf_toSetoid** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：sInf_toSetoid (S : Set (RingCon R)) : (sInf S).toSetoid = sInf ((·.toSetoi
d) '' S)
参数：S : Set (RingCon R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The infimum of a set of congruence relations is the same as the infimum of the s
et's image
under the map to the underlying equivalence relation.
-/
theorem sInf_toSetoid (S : Set (RingCon R)) : (sInf S).toSetoid = sInf ((·.toSetoid) '' S) :=
  Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying binary relation. -/
@[simp, norm_cast]
/-
**RingCon.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_sInf (S : Set (RingCon R)) : ⇑(sInf S) = sInf ((⇑) '' S)
参数：S : Set (RingCon R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The infimum of a set of congruence relations is the same as the infimum of the s
et's image
under the map to the underlying binary relation.
-/
theorem coe_sInf (S : Set (RingCon R)) : ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext; simp only [sInf_image, iInf_apply, iInf_Prop_eq]; rfl

@[simp, norm_cast]
/-
**RingCon.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_iInf {ι : Sort*} (f : ι -> RingCon R) : ⇑(iInf f) = ⨅ i, ⇑(f i)
参数：f : ι -> RingCon R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `RingCon.coe_sInf`：coe_sInf (S : Set (RingCon R)) : ⇑(sInf S) = sInf ((⇑)
 '' S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem coe_iInf {ι : Sort*} (f : ι → RingCon R) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf, coe_sInf, ← Set.range_comp, sInf_range, Function.comp_def]
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (RingCon R) where
  le_refl _c _ _ := id
  le_trans _c1 _c2 _c3 h1 h2 _x _y h := h2 <| h1 h
  le_antisymm _c _d hc hd := ext fun _x _y => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with multiplication and
addition. -/
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete lattice of congruence relations on a given type with multiplication
 and
addition.
-/
instance : CompleteLattice (RingCon R) where
  __ := completeLatticeOfInf (RingCon R) fun s =>
    ⟨fun r hr x y h => (h : ∀ r ∈ s, (r : RingCon R) x y) r hr,
      fun _r hr _x _y h _r' hr' => hr hr' h⟩
  inf c d :=
    { toSetoid := c.toSetoid ⊓ d.toSetoid
      mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩
      add' := fun h1 h2 => ⟨c.add h1.1 h2.1, d.add h1.2 h2.2⟩ }
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top :=
    { (⊤ : Setoid R) with
      mul' := fun _ _ => trivial
      add' := fun _ _ => trivial }
  le_top _ := fun _ _ _h => trivial
  bot :=
    { (⊥ : Setoid R) with
      mul' := congr_arg₂ _
      add' := congr_arg₂ _ }
  bot_le c := fun x _y h => h ▸ c.refl x
/-
**RingCon.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R], ⇑⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : ⇑(⊤ : RingCon R) = ⊤ := rfl
/-
**RingCon.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R], ⇑⊥ = Eq
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : ⇑(⊥ : RingCon R) = Eq := rfl
/-
**RingCon.toCon_top** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R], ⊤.toCon = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCon_top : (⊤ : RingCon R).toCon = ⊤ := rfl
/-
**RingCon.toCon_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R], ⊥.toCon = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCon_bot : (⊥ : RingCon R).toCon = ⊥ := rfl
/-
**RingCon.toCon_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R] {c : RingCon R}, c.toCon 
= ⊤ ↔ c = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingCon.toCon_top`：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R], ⊤.t
oCon = ⊤
· 使用定理 `RingCon.toCon_inj`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] {c d
 : RingCon R}, c.toCon = d.toCon ↔ c = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toCon_eq_top : c.toCon = ⊤ ↔ c = ⊤ := by rw [← toCon_top, toCon_inj]
/-
**RingCon.toCon_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R] {c : RingCon R}, c.toCon 
= ⊥ ↔ c = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingCon.toCon_bot`：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R], ⊥.t
oCon = ⊥
· 使用定理 `RingCon.toCon_inj`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] {c d
 : RingCon R}, c.toCon = d.toCon ↔ c = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toCon_eq_bot : c.toCon = ⊥ ↔ c = ⊥ := by rw [← toCon_bot, toCon_inj]
/-
**RingCon.subsingleton_quotient** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R] {c : RingCon R}, Subsingl
eton c.Quotient ↔ c = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma subsingleton_quotient : Subsingleton c.Quotient ↔ c = ⊤ := by simp [RingCon.Quotient]
/-
**RingCon.nontrivial_quotient** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R] {c : RingCon R}, Nontrivi
al c.Quotient ↔ c ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma nontrivial_quotient : Nontrivial c.Quotient ↔ c ≠ ⊤ := by
  simp [← not_subsingleton_iff_nontrivial]

/-- The infimum of two congruence relations equals the infimum of the underlying binary
operations. -/
@[simp, norm_cast]
/-
**RingCon.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_inf {c d : RingCon R} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of two congruence relations equals the infimum of the underlying bin
ary
operations.
-/
theorem coe_inf {c d : RingCon R} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d := rfl

/-- Definition of the infimum of two congruence relations. -/
/-
**RingCon.inf_iff_and** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：inf_iff_and {c d : RingCon R} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of the infimum of two congruence relations.
-/
theorem inf_iff_and {c d : RingCon R} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (RingCon R) where
  exists_pair_ne :=
    let ⟨x, y, ne⟩ := exists_pair_ne R
    ⟨⊥, ⊤, ne_of_apply_ne (· x y) <| by simp [ne]⟩
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton R] : Subsingleton (RingCon R) where
  allEq c c' := ext fun r r' ↦ by simp_rw [Subsingleton.elim r' r, c.refl, c'.refl]
/-
**RingCon.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：nontrivial_iff : Nontrivial (RingCon R) ↔ Nontrivial R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `RingCon.instSubsingleton`：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul 
R] [Subsingleton R], Subsingleton (RingCon R)
· 使用定理 `RingCon.instNontrivial`：∀ {R : Type u_3} [inst : Add R] [inst_1 : Mul R]
 [Nontrivial R], Nontrivial (RingCon R)
-/
theorem nontrivial_iff : Nontrivial (RingCon R) ↔ Nontrivial R := by
  cases subsingleton_or_nontrivial R
  on_goal 1 => simp_rw [← not_subsingleton_iff_nontrivial, not_iff_not]
  all_goals exact iff_of_true inferInstance ‹_›
/-
**RingCon.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：subsingleton_iff : Subsingleton (RingCon R) ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subsingleton_iff : Subsingleton (RingCon R) ↔ Subsingleton R := by
  simp_rw [← not_nontrivial_iff_subsingleton, nontrivial_iff]
/-
**RingCon.le_ringConGen** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：le_ringConGen {r : R -> R -> Prop} : r <= ⇑(ringConGen r)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_ringConGen {r : R → R → Prop} : r ≤ ⇑(ringConGen r) :=
  RingConGen.Rel.of

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
the infimum of the set of congruence relations containing `r`. -/
/-
**RingCon.ringConGen_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_eq (r : R -> R -> Prop) : ringConGen r = sInf {s : RingCon R | 
forall x y, r x y -> s x y}
参数：r : R -> R -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
· 使用定理 `RingCon.symm`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) {x y : R}, c x y → c y x
· 使用定理 `RingCon.trans`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Rin
gCon R) {x y z : R}, c x y → c y z → c x z
· 使用定理 `RingCon.add`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w + y) (x + z)
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `RingCon.le_ringConGen`：le_ringConGen {r : R -> R -> Prop} : r <= ⇑(ringC
onGen r)

--- 原说明 ---
The inductively defined smallest congruence relation containing a binary relatio
n `r` equals
the infimum of the set of congruence relations containing `r`.
-/
theorem ringConGen_eq (r : R → R → Prop) :
    ringConGen r = sInf {s : RingCon R | ∀ x y, r x y → s x y} :=
  le_antisymm
    (fun _x _y H =>
      RingConGen.Rel.recOn H (fun _ _ h _ hs => hs _ _ h) (RingCon.refl _)
        (fun _ => RingCon.symm _) (fun _ _ => RingCon.trans _)
        (fun _ _ h1 h2 c hc => c.add (h1 c hc) <| h2 c hc)
        (fun _ _ h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc))
    (sInf_le le_ringConGen)

/-- The smallest congruence relation containing a binary relation `r` is contained in any
congruence relation containing `r`. -/
/-
**RingCon.ringConGen_le** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_le {r : R -> R -> Prop} {c : RingCon R} : ringConGen r <= c ↔ r
 <= ⇑c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `RingCon.le_ringConGen`：le_ringConGen {r : R -> R -> Prop} : r <= ⇑(ringC
onGen r)
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingCon.ringConGen_eq`：ringConGen_eq (r : R -> R -> Prop) : ringConGen r
 = sInf {s : RingCon R | forall x y, r x y -> s x y}

--- 原说明 ---
The smallest congruence relation containing a binary relation `r` is contained i
n any
congruence relation containing `r`.
-/
theorem ringConGen_le {r : R → R → Prop} {c : RingCon R} : ringConGen r ≤ c ↔ r ≤ ⇑c :=
  ⟨le_trans le_ringConGen, ringConGen_eq r ▸ fun h => sInf_le h⟩

variable (R) in
/-- There is a Galois insertion of congruence relations on a type with multiplication and addition
`R` into binary relations on `R`. -/
/-
**RingCon.gi** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：(R : Type u_3) → [inst : Add R] → [inst_1 : Mul R] → GaloisInsertion ringC
onGen DFunLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ringConGen_le`：ringConGen_le {r : R -> R -> Prop} {c : RingCon R
} : ringConGen r <= c ↔ r <= ⇑c

--- 原说明 ---
There is a Galois insertion of congruence relations on a type with multiplicatio
n and addition
`R` into binary relations on `R`.
-/
protected def gi : GaloisInsertion (ringConGen (R := R)) (⇑) where
  choice r _h := ringConGen r
  gc _r _ := ringConGen_le
  le_l_u _ := le_ringConGen
  choice_eq _ _ := rfl
/-
**RingCon.ringConGen_monotone** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_monotone : Monotone (ringConGen (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem ringConGen_monotone : Monotone (ringConGen (R := R)) :=
  RingCon.gi R |>.gc.monotone_l

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
containing `s` contains the smallest congruence relation containing `r`. -/
@[gcongr]
/-
**RingCon.ringConGen_mono** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_mono {r s : R -> R -> Prop} (h : forall x y, r x y -> s x y) : 
ringConGen r <= ringConGen s
参数：h : forall x y, r x y -> s x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ringConGen_monotone`：ringConGen_monotone : Monotone (ringConGen 
(R

--- 原说明 ---
Given binary relations `r, s` with `r` contained in `s`, the smallest congruence
 relation
containing `s` contains the smallest congruence relation containing `r`.
-/
theorem ringConGen_mono {r s : R → R → Prop} (h : ∀ x y, r x y → s x y) :
    ringConGen r ≤ ringConGen s :=
  ringConGen_monotone h

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
/-
**RingCon.ringConGen_of_ringCon** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_of_ringCon (c : RingCon R) : ringConGen c = c
参数：c : RingCon R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Congruence relations equal the smallest congruence relation in which they are co
ntained.
-/
theorem ringConGen_of_ringCon (c : RingCon R) : ringConGen c = c :=
  RingCon.gi R |>.l_u_eq _

/-- The map sending a binary relation to the smallest congruence relation in which it is
contained is idempotent. -/
/-
**RingCon.ringConGen_idem** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_idem (r : R -> R -> Prop) : ringConGen (ringConGen r) = ringCon
Gen r
参数：r : R -> R -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The map sending a binary relation to the smallest congruence relation in which i
t is
contained is idempotent.
-/
theorem ringConGen_idem (r : R → R → Prop) : ringConGen (ringConGen r) = ringConGen r :=
  RingCon.gi R |>.gc.l_u_l_eq_l _
/-
**RingCon.ringConGen_sup** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_sup (r s : R -> R -> Prop) : ringConGen (r ⊔ s) = ringConGen r 
⊔ ringConGen s
参数：r s : R -> R -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem ringConGen_sup (r s : R → R → Prop) : ringConGen (r ⊔ s) = ringConGen r ⊔ ringConGen s :=
  RingCon.gi R |>.gc.l_sup
/-
**RingCon.ringConGen_sSup** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_sSup (rs : Set (R -> R -> Prop)) : ringConGen (sSup rs) = ⨆ r i
n rs, ringConGen r
参数：rs : Set (R -> R -> Prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem ringConGen_sSup (rs : Set (R → R → Prop)) : ringConGen (sSup rs) = ⨆ r ∈ rs, ringConGen r :=
  RingCon.gi R |>.gc.l_sSup
/-
**RingCon.ringConGen_iSup** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ringConGen_iSup {ι : Sort*} (r : ι -> R -> R -> Prop) : ringConGen (iSup r
) = ⨆ i, ringConGen (r i)
参数：r : ι -> R -> R -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem ringConGen_iSup {ι : Sort*} (r : ι → R → R → Prop) :
    ringConGen (iSup r) = ⨆ i, ringConGen (r i) :=
  RingCon.gi R |>.gc.l_iSup

/-- The supremum of two congruence relations equals the smallest congruence relation containing
the supremum of the underlying binary operations. -/
/-
**RingCon.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：sup_def (c d : RingCon R) : c ⊔ d = ringConGen (⇑c ⊔ ⇑d)
参数：c d : RingCon R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b

--- 原说明 ---
The supremum of two congruence relations equals the smallest congruence relation
 containing
the supremum of the underlying binary operations.
-/
theorem sup_def (c d : RingCon R) : c ⊔ d = ringConGen (⇑c ⊔ ⇑d) :=
  RingCon.gi R |>.l_sup_u _ _ |>.symm

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
the binary relation '`x` is related to `y` by `c` or `d`'. -/
/-
**RingCon.sup_eq_ringConGen** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：sup_eq_ringConGen (c d : RingCon R) : c ⊔ d = ringConGen fun x y => c x y 
∨ d x y
参数：c d : RingCon R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.sup_def`：sup_def (c d : RingCon R) : c ⊔ d = ringConGen (⇑c ⊔ ⇑d
)

--- 原说明 ---
The supremum of congruence relations `c, d` equals the smallest congruence relat
ion containing
the binary relation '`x` is related to `y` by `c` or `d`'.
-/
theorem sup_eq_ringConGen (c d : RingCon R) : c ⊔ d = ringConGen fun x y => c x y ∨ d x y :=
  sup_def c d

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
containing the supremum of the set's image under the map to the underlying binary relation. -/
/-
**RingCon.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：sSup_def (S : Set (RingCon R)) : sSup S = ringConGen (sSup ((⇑) '' S))
参数：S : Set (RingCon R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisInsertion.l_sSup_u_image`：l_sSup_u_image [CompleteLattice α] [Comp
leteLattice β] (gi : GaloisInsertion l u) (s : Set β) : l (sSup (u '' s)) = sSup
 s

--- 原说明 ---
The supremum of a set of congruence relations is the same as the smallest congru
ence relation
containing the supremum of the set's image under the map to the underlying binar
y relation.
-/
theorem sSup_def (S : Set (RingCon R)) : sSup S = ringConGen (sSup ((⇑) '' S)) :=
  RingCon.gi R |>.l_sSup_u_image _ |>.symm

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by `c`'. -/
/-
**RingCon.sSup_eq_ringConGen** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：sSup_eq_ringConGen (S : Set (RingCon R)) : sSup S = ringConGen fun x y => 
exists c : RingCon R, c in S ∧ c x y
参数：S : Set (RingCon R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingCon.sSup_def`：sSup_def (S : Set (RingCon R)) : sSup S = ringConGen (
sSup ((⇑) '' S))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The supremum of a set of congruence relations `S` equals the smallest congruence
 relation
containing the binary relation 'there exists `c ∈ S` such that `x` is related to
 `y` by `c`'.
-/
theorem sSup_eq_ringConGen (S : Set (RingCon R)) :
    sSup S = ringConGen fun x y => ∃ c : RingCon R, c ∈ S ∧ c x y := by
  rw [sSup_def]
  congr! with x y
  simp

open scoped Function
/-
**RingCon.le_comap_ringConGen** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：le_comap_ringConGen {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass
 F R' R] (r : R -> R -> Prop) (f : F) : ringConGen (r on f) <= (ringConGen r).co
map f
参数：r : R -> R -> Prop；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingCon.ringConGen_le`：ringConGen_le {r : R -> R -> Prop} {c : RingCon R
} : ringConGen r <= c ↔ r <= ⇑c
-/
theorem le_comap_ringConGen {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R]
    (r : R → R → Prop) (f : F) :
    ringConGen (r on f) ≤ (ringConGen r).comap f :=
  ringConGen_le.2 fun _ _ h => RingConGen.Rel.of _ _ h
/-
**RingCon.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_injective {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R
' R] (f : F) (hf : Function.Surjective f) : Function.Injective (comap · f)
参数：f : F；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Con.comap_injective`：comap_injective (f : M -> N) (hf : Function.Surject
ive f) (hf') : Function.Injective (comap f hf')
· 使用引理 `RingCon.toCon_injective`：toCon_injective : Injective fun c : RingCon R =
> c.toCon
-/
theorem comap_injective {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R]
    (f : F) (hf : Function.Surjective f) :
    Function.Injective (comap · f) :=
  .of_comp (f := toCon) <| (Con.comap_injective f hf <| map_mul f).comp toCon_injective
/-
**RingCon.comap_ringConGen_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_ringConGen_ringEquiv {R R'} [NonAssocSemiring R] [NonAssocSemiring R
'] (r : R' -> R' -> Prop) (f : R ≃+* R') : (ringConGen r).comap f = ringConGen (
r on f)
参数：r : R' -> R' -> Prop；f : R ≃+* R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `RingCon.comap_mono`：comap_mono {F : Type*} [FunLike F R R'] [AddHomClass
 F R R'] [MulHomClass F R R'] {J J' : RingCon R'} {f : F} (h : J <= J') : J.coma
p f <= J…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `RingCon.le_comap_ringConGen`：le_comap_ringConGen {F} [FunLike F R' R] [M
ulHomClass F R' R] [AddHomClass F R' R] (r : R -> R -> Prop) (f : F) : ringConGe
n (r on f) <= (ri…
· 使用定理 `RingCon.ringConGen_mono`：ringConGen_mono {r s : R -> R -> Prop} (h : for
all x y, r x y -> s x y) : ringConGen r <= ringConGen s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingCon.comap_nonUnitalRingHomComp`：comap_nonUnitalRingHomComp {R R' R''
} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R'] [NonUnitalNonAsso
cSemiring R''] (J : Ring…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingCon.comap.congr_simp`：∀ {R : Type u_2} {R' : Type u_3} {F : Type u_4
} [inst : Add R] [inst_1 : Add R'] [inst_2 : FunLike F R R']   [inst_3 : AddHomC
lass F R R'] […
· 使用定理 `RingEquiv.symm_toNonUnitalRingHom_comp_toNonUnitalRingHom`：symm_toNonUni
talRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) : e.symm.toNonUnitalRingHom.com
p e.toNonUnitalRingHom = NonUnitalRingHom.id _
-/
theorem comap_ringConGen_ringEquiv {R R'} [NonAssocSemiring R] [NonAssocSemiring R']
    (r : R' → R' → Prop) (f : R ≃+* R') :
    (ringConGen r).comap f = ringConGen (r on f) := by
  refine le_antisymm ?_ (le_comap_ringConGen _ _)
  trans (ringConGen (r on ⇑f) |>.comap f.symm.toNonUnitalRingHom).comap f.toNonUnitalRingHom
  · apply comap_mono
    grw [← le_comap_ringConGen]
    gcongr
    simp [Function.onFun, RingEquiv.coe_toNonUnitalRingHom']
  · rw [← comap_nonUnitalRingHomComp]
    simp

-- This one probably needs the RingCon version of `Setoid.comap_surjective`
proof_wanted comap_ringConGen_equiv
    {F} [FunLike F R' R] [MulHomClass F R' R] [AddHomClass F R' R] [EquivLike F R' R]
    (r : R → R → Prop) (f : F) :
    (ringConGen r).comap f = ringConGen (r on f)

end Lattice

end RingCon

