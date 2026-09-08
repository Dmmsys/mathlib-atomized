/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Congruence relations and ring homomorphisms

This file contains elementary definitions involving congruence
relations and morphisms for rings and semirings

## Main definitions

* `RingCon.ker`: the kernel of a monoid homomorphism as a congruence relation
* `RingCon.lift`, `RingCon.liftₐ`: the homomorphism / the algebra morphism
  on the quotient given that the congruence is in the kernel
* `RingCon.map`, `RingCon.mapₐ`: homomorphism / algebra morphism
  from a smaller to a larger quotient

* `RingCon.quotientKerEquivRangeS`, `RingCon.quotientKerEquivRange`,
  `RingCon.quotientKerEquivRangeₐ` :
  the first isomorphism theorem for semirings (using `RingHom.rangeS`),
  rings (using `RingHom.range`) and algebras (using `AlgHom.range`).
* `RingCon.comapQuotientEquivRangeS`, `RingCon.comapQuotientEquivRange`,
  `RingCon.comapQuotientEquivRangeₐ` : the second isomorphism theorem
  for semirings (using `RingHom.rangeS`), rings (using `RingHom.range`)
  and algebras (using `AlgHom.range`).

* `RingCon.quotientQuotientEquivQuotient`, `RingCon.quotientQuotientEquivQuotientₐ` :
  the third isomorphism theorem for semirings (or rings) and algebras

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, ring,
quotient ring
-/

@[expose] public section

variable {M : Type*} {N : Type*} {P : Type*}

open Function Setoid

namespace RingCon

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P] {c d : RingCon M}

/-- The kernel of a ring homomorphism as a ring congruence relation. -/
/-
**RingCon.ker** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：ker (f : M ->+* N) : RingCon M
参数：f : M ->+* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a ring homomorphism as a ring congruence relation.
-/
def ker (f : M →+* N) : RingCon M := comap ⊥ f
/-
**RingCon.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_bot (f : M ->+* N) : comap ⊥ f = ker f
参数：f : M ->+* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem comap_bot (f : M →+* N) : comap ⊥ f = ker f := rfl

/-- The definition of the ring congruence relation defined by a ring homomorphism's kernel. -/
@[simp]
/-
**RingCon.ker_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ker_apply (f : M ->+* N) {x y} : ker f x y ↔ f x = f y
参数：f : M ->+* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The definition of the ring congruence relation defined by a ring homomorphism's 
kernel.
-/
theorem ker_apply (f : M →+* N) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

/-- The kernel of the quotient map induced by a ring congruence relation `c` equals `c`. -/
/-
**RingCon.ker_mk'_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} [inst : NonAssocSemiring M] (c : RingCon M), RingCon.ker 
c.mk' = c
参数：c : RingCon M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext`：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c =
 d
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b

--- 原说明 ---
The kernel of the quotient map induced by a ring congruence relation `c` equals 
`c`.
-/
theorem ker_mk'_eq (c : RingCon M) : ker c.mk' = c :=
  ext fun _ _ => Quotient.eq''
/-
**RingCon.ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ker_comp {f : M ->+* N} {g : N ->+* P} : ker (g.comp f) = (ker g).comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext`：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c =
 d
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_comp {f : M →+* N} {g : N →+* P} :
    ker (g.comp f) = (ker g).comap f :=
  ext fun x y ↦ by simp [ker_apply, comap_rel]
/-
**RingCon.comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_eq {g : N ->+* M} : c.comap g = ker (c.mk'.comp g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingCon.ker_comp`：ker_comp {f : M ->+* N} {g : N ->+* P} : ker (g.comp f
) = (ker g).comap f
· 使用定理 `RingCon.ker_mk'_eq`：∀ {M : Type u_1} [inst : NonAssocSemiring M] (c : Ri
ngCon M), RingCon.ker c.mk' = c
-/
theorem comap_eq {g : N →+* M} :
    c.comap g = ker (c.mk'.comp g) := by
  rw [ker_comp, ker_mk'_eq]

/-- An isomorphism of rings `e : M ≃+* N` generates an isomorphism between quotient spaces,
if it is compatible with the relations. -/
/-
**RingCon.congr** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     [inst : NonAssocSemiring M] →     
  [inst_1 : NonAssocSemiring N] →         {c : RingCon M} → {d : RingCon N} → (e
 : M ≃+* N) → c = d.comap e → c.Quotient ≃+* d.Quotient
参数：e : M ≃+* N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of rings `e : M ≃+* N` generates an isomorphism between quotient 
spaces,
if it is compatible with the relations.
-/
protected def congr {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) :
    c.Quotient ≃+* d.Quotient where
  __ := Quotient.congr e <| by apply RingCon.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)
  map_add' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_add x y)
/-
**RingCon.congr_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] {c : RingCon M}   {d : RingCon N} (e : M ≃+* N) (h : c = d.comap
 e) (a : M), (RingCon.congr e h) ↑a = ↑(e a)
参数：e : M ≃+* N；h : c = d.comap e；a : M；RingCon.congr e h；e a。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] theorem congr_mk {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) (a : M) :
    RingCon.congr e h (a : c.Quotient) = (e a : d.Quotient) := rfl
/-
**RingCon.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] {c : RingCon M}   {d : RingCon N} (e : M ≃+* N) (h : c = d.comap
 e), (RingCon.congr e h).symm = RingCon.congr e.symm ⋯
参数：e : M ≃+* N；h : c = d.comap e；RingCon.congr e h。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
@[simp] theorem congr_symm {c : RingCon M} {d : RingCon N} (e : M ≃+* N) (h : c = d.comap e) :
    (RingCon.congr e h).symm =
      RingCon.congr e.symm (ext <| e.surjective.forall₂.2 <| by simp [h]) :=
  rfl

/-- Given a function `f`, the smallest ring congruence relation containing the binary
relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to
the elements of `f⁻¹(y)` by a ring congruence relation `c`.' -/
/-
**RingCon.mapGen** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：mapGen {c : RingCon M} (f : M -> N) : RingCon N
参数：f : M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f`, the smallest ring congruence relation containing the binar
y
relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are rel
ated to
the elements of `f⁻¹(y)` by a ring congruence relation `c`.'
-/
def mapGen {c : RingCon M} (f : M → N) : RingCon N :=
  ringConGen <| Relation.Map c f f

/-- If `c` is a ring congruence on `M`, then the smallest ring
congruence relation on `N` deduced from `c` by a ring homomorphism
from `M` to `N` is the relation deduced from `c`. -/
/-
**RingCon.mapGen_eq_map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：mapGen_eq_map_of_surjective {c : RingCon M} (f : M ->+* N) (h : ker f <= c
) (hf : Surjective f) : c.mapGen f = Relation.Map c f f
参数：f : M ->+* N；h : ker f <= c；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Relation.map_equivalence`：map_equivalence {r : α -> α -> Prop} (hr : Equ
ivalence r) (f : α -> β) (hf : f.Surjective) (hf_ker : forall x y, f x = f y -> 
r x y) : Equiv…
· 使用定理 `Setoid.iseqv`：∀ {α : Sort u} [self : Setoid α], Equivalence ⇑self
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `RingCon.add`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w + y) (x + z)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
If `c` is a ring congruence on `M`, then the smallest ring
congruence relation on `N` deduced from `c` by a ring homomorphism
from `M` to `N` is the relation deduced from `c`.
-/
theorem mapGen_eq_map_of_surjective
    {c : RingCon M} (f : M →+* N) (h : ker f ≤ c) (hf : Surjective f) :
    c.mapGen f = Relation.Map c f f := by
  refine le_antisymm ?_ <| (RingCon.gi N).gc.le_u_l _
  have := Relation.map_equivalence c.toSetoid.2 _ hf h
  intro _ _ hg
  induction hg with
  | of _ _ a => exact a
  | refl x => exact this.refl x
  | symm _ h => exact this.symm h
  | trans _ _ h₁ h₂ => exact this.trans h₁ h₂
  | add _ _ h₁ h₂ =>
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a + p, b + q, c.add h1 h2, map_add f _ _, map_add f _ _⟩
  | mul _ _ h₁ h₂ =>
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩
/-
**RingCon.mapGen_apply_apply_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：mapGen_apply_apply_of_surjective {c : RingCon M} (f : M ->+* N) (h : ker f
 <= c) (hf : Surjective f) {x y : M} : c.mapGen f (f x) (f y) ↔ c x y
参数：f : M ->+* N；h : ker f <= c；hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingCon.mapGen_eq_map_of_surjective`：mapGen_eq_map_of_surjective {c : Ri
ngCon M} (f : M ->+* N) (h : ker f <= c) (hf : Surjective f) : c.mapGen f = Rela
tion.Map c f f
· 使用引理 `Relation.map_apply`：map_apply : Relation.Map r f g c d ↔ exists a b, r a
 b ∧ f a = c ∧ g b = d
· 使用定理 `RingCon.trans`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Rin
gCon R) {x y z : R}, c x y → c y z → c x z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mapGen_apply_apply_of_surjective
    {c : RingCon M} (f : M →+* N) (h : ker f ≤ c) (hf : Surjective f) {x y : M} :
    c.mapGen f (f x) (f y) ↔ c x y := by
  rw [mapGen_eq_map_of_surjective f h hf, Relation.map_apply]
  refine ⟨fun ⟨a, b, h₁, h₂, h₃⟩ ↦ ?_, by grind⟩
  exact c.trans (h h₂.symm) <| c.trans h₁ <| h h₃

set_option backward.isDefEq.respectTransparency false in
/-- Given a ring congruence relation `c` on a semiring `M`, the order-preserving
bijection between the set of ring congruence relations containing `c` and the
ring congruence relations on the quotient of `M` by `c`. -/
/-
**RingCon.correspondence** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：correspondence {c : RingCon M} : Set.Ici c ≃o RingCon c.Quotient where toF
un d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring congruence relation `c` on a semiring `M`, the order-preserving
bijection between the set of ring congruence relations containing `c` and the
ring congruence relations on the quotient of `M` by `c`.
-/
def correspondence {c : RingCon M} : Set.Ici c ≃o RingCon c.Quotient where
  toFun d := d.1.mapGen c.mk'
  invFun d := ⟨d.comap (mk' c), c.ker_mk'_eq.symm.trans_le <| comap_bot c.mk' ▸ comap_mono bot_le⟩
  left_inv d := by
    ext
    simp only [comap_rel]
    rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le d.2) c.mk'_surjective]
  right_inv d := by
    ext x y
    simp only
    obtain ⟨x, rfl⟩ := c.mk'_surjective x
    obtain ⟨y, rfl⟩ := c.mk'_surjective y
    rw [mapGen_apply_apply_of_surjective _ (comap_bot c.mk' ▸ comap_mono bot_le) c.mk'_surjective,
      comap_rel]
  map_rel_iff' {s t} := by
    simp only [Equiv.coe_fn_mk, le_def, c.mk'_surjective.forall, ← Subtype.coe_le_coe]
    simp_rw [mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le s.2) c.mk'_surjective,
      mapGen_apply_apply_of_surjective c.mk' (c.ker_mk'_eq.trans_le t.2) c.mk'_surjective]

variable (c : RingCon M)

variable (x y : M)

variable (f : M →+* P)

/-- The homomorphism on the quotient of a ring by a congruence relation `c`
induced by a homomorphism constant on the equivalence classes of `c`. -/
/-
**RingCon.lift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：lift (H : c <= ker f) : c.Quotient ->+* P where __
参数：H : c <= ker f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1

--- 原说明 ---
The homomorphism on the quotient of a ring by a congruence relation `c`
induced by a homomorphism constant on the equivalence classes of `c`.
-/
def lift (H : c ≤ ker f) : c.Quotient →+* P where
  __ := c.toAddCon.lift f.toAddMonoidHom H
  map_one' := f.map_one
  map_mul' x y := Con.induction_on₂ x y fun m n => f.map_mul m n

variable {c f}

/-- The diagram describing the universal property for quotients of ring commutes. -/
/-
**RingCon.lift_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_mk' (H : c <= ker f) (x) : c.lift f H (c.mk' x) = f x
参数：H : c <= ker f；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram describing the universal property for quotients of ring commutes.
-/
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
/-
**RingCon.lift_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] {c : RingCon M} {f : M →+* P}   (H : c ≤ RingCon.ker f) (x : M),
 (c.lift f H) ↑x = f x
参数：H : c ≤ RingCon.ker f；x : M；c.lift f H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram describing the universal property for quotients of rings commutes.
-/
@[simp] theorem lift_coe (H : c ≤ ker f) (x : M) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
/-
**RingCon.lift_comp_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] {c : RingCon M} {f : M →+* P}   (H : c ≤ RingCon.ker f), (c.lift
 f H).comp c.mk' = f
参数：H : c ≤ RingCon.ker f；c.lift f H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram describing the universal property for quotients of rings commutes.
-/
@[simp] theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := rfl

/-- Given a homomorphism `f` from the quotient of a ring by a ring congruence
relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the ring to the quotient. -/
/-
**RingCon.lift_apply_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_apply_mk' (f : c.Quotient ->+* P) : (c.lift (f.comp c.mk') fun x y h 
=> show f ↑x = f ↑y by rw [c.eq.2 h]) = f
参数：f : c.Quotient ->+* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g

--- 原说明 ---
Given a homomorphism `f` from the quotient of a ring by a ring congruence
relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the ring to the quotient.
-/
theorem lift_apply_mk' (f : c.Quotient →+* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring. -/
@[ext high] -- This should have higher priority than `RingHom.ext`
/-
**RingCon.Quotient.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `RingCon.Quotient`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] {c : RingCon M}   {f g : c.Quotient →+* P}, f.comp c.mk' = g.com
p c.mk' → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `RingCon.mk'_surjective`：∀ {R : Type u_1} [inst : NonAssocSemiring R] (c 
: RingCon R), Function.Surjective ⇑c.mk'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring.
-/
theorem Quotient.hom_ext {f g : c.Quotient →+* P} (h : f.comp c.mk' = g.comp c.mk') : f = g :=
  DFunLike.ext _ _ <| c.mk'_surjective.forall.mpr fun x ↦ by exact congr($h x)

/-- The uniqueness part of the universal property for quotients of rings. -/
/-
**RingCon.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_unique (H : c <= ker f) (g : c.Quotient ->+* P) (Hg : g.comp c.mk' = 
f) : g = c.lift f H
参数：H : c <= ker f；g : c.Quotient ->+* P；Hg : g.comp c.mk' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.Quotient.hom_ext`：∀ {M : Type u_1} {P : Type u_3} [inst : NonAss
ocSemiring M] [inst_1 : NonAssocSemiring P] {c : RingCon M}   {f g : c.Quotient 
→+* P}, f.comp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The uniqueness part of the universal property for quotients of rings.
-/
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →+* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  Quotient.hom_ext (by aesop)

/-- Surjective ring homomorphisms constant on the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient. -/
/-
**RingCon.lift_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_surjective_iff {h : c <= ker f} : Surjective (c.lift f h) ↔ Surjectiv
e f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quot.surjective_lift`：∀ {α : Sort u_1} {γ : Sort u_4} {r : α → α → Prop}
 {f : α → γ} (h : ∀ (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂),   Function.Surjective (
Quot.lift …
· 使用定理 `AddCon.lift_surjective_of_surjective`：∀ {M : Type u_1} {P : Type u_3} [i
nst : AddZeroClass M] [inst_1 : AddZeroClass P] {c : AddCon M} {f : M →+ P}   (h
 : c ≤ AddCon.ker f), Func…

--- 原说明 ---
Surjective ring homomorphisms constant on the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient.
-/
theorem lift_surjective_iff {h : c ≤ ker f} :
    Surjective (c.lift f h) ↔ Surjective f := by
  refine ⟨fun H ↦ (Quot.surjective_lift fun x x_1 h_1 ↦ h h_1).mp H,
    fun H ↦ AddCon.lift_surjective_of_surjective h H⟩

/-- Surjective ring homomorphisms constant on the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient. -/
/-
**RingCon.lift_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_surjective_of_surjective (h : c <= ker f) (hf : Surjective f) : Surje
ctive (c.lift f h)
参数：h : c <= ker f；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingCon.lift_surjective_iff`：lift_surjective_iff {h : c <= ker f} : Surj
ective (c.lift f h) ↔ Surjective f

--- 原说明 ---
Surjective ring homomorphisms constant on the equivalence classes
of a ring congruence relation induce a surjective homomorphism on the quotient.
-/
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) :=
  lift_surjective_iff.mpr hf

/-- Given a ring homomorphism `f` from `M` to `P` whose kernel contains `c`,
the lift of `M` to `P` is injective iff `ker f = c`. -/
/-
**RingCon.lift_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_injective_iff {h : c <= ker f} : Function.Injective (c.lift f h) ↔ c 
= ker f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext''`：ext'' {c d : RingCon R} (H : c.toSetoid = d.toSetoid) : c
 = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Setoid.ker_eq_lift_of_injective`：ker_eq_lift_of_injective {r : Setoid α}
 (f : α -> β) (H : r <= ker f) (h : Injective (Quotient.lift f H)) : ker f = r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Given a ring homomorphism `f` from `M` to `P` whose kernel contains `c`,
the lift of `M` to `P` is injective iff `ker f = c`.
-/
theorem lift_injective_iff {h : c ≤ ker f} :
    Function.Injective (c.lift f h) ↔ c = ker f := by
  refine ⟨fun H ↦ ext'' (Setoid.ker_eq_lift_of_injective f h H).symm, ?_⟩
  rintro H ⟨x⟩ ⟨y⟩
  simp [H]
/-
**RingCon.lift_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：lift_bijective_iff {h : c <= ker f} : Function.Bijective (c.lift f h) ↔ c 
= ker f ∧ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_bijective_iff {h : c ≤ ker f} :
    Function.Bijective (c.lift f h) ↔ c = ker f ∧ Surjective f := by
  unfold Function.Bijective
  simp only [lift_injective_iff, lift_surjective_iff]

/-- Given a ring homomorphism `f` from `M` to `P`, the kernel of `f` is the
unique ring congruence relation on `M` whose induced map from the quotient of
`M` to `P` is injective. -/
/-
**RingCon.ker_eq_lift_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ker_eq_lift_of_injective (H : c <= ker f) (h : Injective (c.lift f H)) : k
er f = c
参数：H : c <= ker f；h : Injective (c.lift f H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingCon.lift_injective_iff`：lift_injective_iff {h : c <= ker f} : Functi
on.Injective (c.lift f h) ↔ c = ker f

--- 原说明 ---
Given a ring homomorphism `f` from `M` to `P`, the kernel of `f` is the
unique ring congruence relation on `M` whose induced map from the quotient of
`M` to `P` is injective.
-/
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  (lift_injective_iff.mp h).symm

variable (f)

/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
/-
**RingCon.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：kerLift : (ker f).Quotient ->+* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism induced on the quotient of a ring by the kernel of a ring homom
orphism.
-/
def kerLift : (ker f).Quotient →+* P :=
  (ker f).lift f fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes. -/
/-
**RingCon.kerLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：kerLift_mk (x : M) : kerLift f x = f x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes.
-/
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
/-
**RingCon.kerLift_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：kerLift_injective (f : M ->+* P) : Injective (kerLift f)
参数：f : M ->+* P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.kerLift_injective`：∀ {M : Type u_1} {P : Type u_3} [inst : AddZer
oClass M] [inst_1 : AddZeroClass P] (f : M →+ P),   Function.Injective ⇑(AddCon.
kerLift f)
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`
's kernel.
-/
theorem kerLift_injective (f : M →+* P) : Injective (kerLift f) :=
  AddCon.kerLift_injective (f : M →+ P)

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
`d`'s quotient map induces a homomorphism from the quotient by `c` to the
quotient by `d`. -/
/-
**RingCon.map** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：map (c d : RingCon M) (h : c <= d) : c.Quotient ->+* d.Quotient
参数：c d : RingCon M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
`d`'s quotient map induces a homomorphism from the quotient by `c` to the
quotient by `d`.
-/
def map (c d : RingCon M) (h : c ≤ d) : c.Quotient →+* d.Quotient :=
  c.lift d.mk' fun x y hc => show ker d.mk' x y from (ker_mk'_eq d).symm ▸ h hc

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
/-
**RingCon.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：map_apply {c d : RingCon M} (h : c <= d) (x) : c.map d h x = c.lift d.mk' 
(fun _ _ hc => d.eq.2 <| h hc) x
参数：h : c <= d；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map.
-/
theorem map_apply {c d : RingCon M} (h : c ≤ d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

end

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P]

variable {c : RingCon M}

/-
**RingCon.rangeS_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} [inst : NonAssocSemiring M] {c : RingCon M}, c.mk'.rangeS
 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.rangeS_eq_top`：rangeS_eq_top : f.rangeS = ⊤ ↔ Function.Surjectiv
e f
· 使用定理 `RingCon.mk'_surjective`：∀ {R : Type u_1} [inst : NonAssocSemiring R] (c 
: RingCon R), Function.Surjective ⇑c.mk'
-/
@[simp] theorem rangeS_mk' : RingHom.rangeS c.mk' = ⊤ :=
  RingHom.rangeS_eq_top.mpr (mk'_surjective _)

variable {f : M →+* P}

/-- Given a congruence relation `c` on a semiring and a homomorphism
`f` constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
/-
**RingCon.rangeS_lift** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] {c : RingCon M} {f : M →+* P}   (H : c ≤ RingCon.ker f), (c.lift
 f H).rangeS = f.rangeS
参数：H : c ≤ RingCon.ker f；c.lift f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_quot_lift`：range_quot_lift {r : ι -> ι -> Prop} (hf : forall x
 y, r x y -> f x = f y) : range (Quot.lift f hf) = range f

--- 原说明 ---
Given a congruence relation `c` on a semiring and a homomorphism
`f` constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient.
-/
@[simp] theorem rangeS_lift (H : c ≤ ker f) :
    RingHom.rangeS (c.lift f H) = f.rangeS :=
  SetLike.coe_injective <| Set.range_quot_lift _

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
/-
**RingCon.rangeS_kerLift** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] {f : M →+* P},   (RingCon.kerLift f).rangeS = f.rangeS
参数：RingCon.kerLift f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.rangeS_lift`：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSem
iring M] [inst_1 : NonAssocSemiring P] {c : RingCon M} {f : M →+* P}   (H : c ≤ 
RingCon.k…

--- 原说明 ---
Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`.
-/
@[simp] theorem rangeS_kerLift :
    RingHom.rangeS (kerLift f) = RingHom.rangeS f :=
  rangeS_lift fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for semirings**. -/
/-
**RingCon.quotientKerEquivRangeS** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivRangeS (f : M ->+* P) : (ker f).Quotient ≃+* f.rangeS wher
e __
参数：f : M ->+* P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
The **first isomorphism theorem for semirings**.
-/
noncomputable def quotientKerEquivRangeS (f : M →+* P) :
    (ker f).Quotient ≃+* f.rangeS where
  __ := RingHom.codRestrict (kerLift f) _ _
  __ := Setoid.quotientKerEquivRange _
/-
**RingCon.coe_quotientKerEquivRangeS_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] (f : M →+* P) (x : M),   ↑((RingCon.quotientKerEquivRangeS f) ↑x
) = f x
参数：f : M →+* P；x : M；(RingCon.quotientKerEquivRangeS f) ↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_quotientKerEquivRangeS_mk (f : M →+* P) (x : M) :
    (quotientKerEquivRangeS f x) = f x := rfl

/-- The first isomorphism theorem for semirings in the case of a homomorphism with right inverse. -/
/-
**RingCon.quotientKerEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivOfRightInverse (f : M ->+* P) (g : P -> M) (hf : Function.
RightInverse g f) : (ker f).Quotient ≃+* P where __
参数：f : M ->+* P；g : P -> M；hf : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first isomorphism theorem for semirings in the case of a homomorphism with r
ight inverse.
-/
def quotientKerEquivOfRightInverse (f : M →+* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃+* P where
  __ := kerLift f
  __ := Setoid.quotientKerEquivOfRightInverse _ _ hf
/-
**RingCon.quotientKerEquivOfRightInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingCo
n`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] (f : M →+* P) (g : P → M)   (hf : Function.RightInverse g ⇑f) (x
 : (RingCon.ker f).Quotient),   (RingCon.quotientKerEquivOfRightInverse f g hf) 
x = (RingCon.kerLift f) x
参数：f : M →+* P；g : P → M；hf : Function.RightInverse g ⇑f；x : (RingCon.ker f).Quo
tient；RingCon.quotientKerEquivOfRightInverse f g hf；RingCon.kerLift f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem quotientKerEquivOfRightInverse_apply
    (f : M →+* P) (g : P → M) (hf : Function.RightInverse g f) (x : (ker f).Quotient) :
    quotientKerEquivOfRightInverse f g hf x = kerLift f x :=
  rfl

/-- The first isomorphism theorem for rings in the case of a surjective homomorphism.

For a `computable` version, see `RingCon.quotientKerEquivOfRightInverse`.
-/
/-
**RingCon.quotientKerEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivOfSurjective (f : M ->+* P) (hf : Surjective f) : (ker f).
Quotient ≃+* P
参数：f : M ->+* P；hf : Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first isomorphism theorem for rings in the case of a surjective homomorphism
.

For a `computable` version, see `RingCon.quotientKerEquivOfRightInverse`.
-/
noncomputable def quotientKerEquivOfSurjective (f : M →+* P) (hf : Surjective f) :
    (ker f).Quotient ≃+* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec
/-
**RingCon.quotientKerEquivOfSurjective_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] (f : M →+* P)   (hf : Function.Surjective ⇑f) (x : M), (RingCon.
quotientKerEquivOfSurjective f hf) ↑x = f x
参数：f : M →+* P；hf : Function.Surjective ⇑f；x : M；RingCon.quotientKerEquivOfSurje
ctive f hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem quotientKerEquivOfSurjective_mk (f : M →+* P) (hf : Surjective f) (x : M) :
    quotientKerEquivOfSurjective f hf x = f x := rfl

/-- A surjective ring homomorphism `f : M →+* N` induces
a ring equivalence `d.Quotient ≃+* c.Quotient`,
whenever `c : RingCon M` and `d : RingCon N` are such that `d = c.comap f`. -/
/-
**RingCon.comapQuotientEquivOfSurj** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：comapQuotientEquivOfSurj (c : RingCon M) (f : N ->+* M) (hf : Function.Sur
jective f) {d : RingCon N} (hcd : d = c.comap f) : d.Quotient ≃+* c.Quotient
参数：c : RingCon M；f : N ->+* M；hf : Function.Surjective f；hcd : d = c.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A surjective ring homomorphism `f : M →+* N` induces
a ring equivalence `d.Quotient ≃+* c.Quotient`,
whenever `c : RingCon M` and `d : RingCon N` are such that `d = c.comap f`.
-/
noncomputable def comapQuotientEquivOfSurj
    (c : RingCon M) (f : N →+* M) (hf : Function.Surjective f)
    {d : RingCon N} (hcd : d = c.comap f) :
    d.Quotient ≃+* c.Quotient :=
  (RingCon.congr (.refl _) (hcd.trans c.comap_eq)).trans
    <| RingCon.quotientKerEquivOfSurjective (c.mk'.comp f)
    (c.mk'_surjective.comp hf)
/-
**RingCon.comapQuotientEquivOfSurj_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] (c : RingCon M) {f : N →+* M}   (hf : Function.Surjective ⇑f) {d
 : RingCon N} (hcd : d = c.comap f) (x : N),   (c.comapQuotientEquivOfSurj f hf 
hcd) ↑x = ↑(f x)
参数：c : RingCon M；hf : Function.Surjective ⇑f；hcd : d = c.comap f；x : N；c.comapQu
otientEquivOfSurj f hf hcd；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
@[simp] lemma comapQuotientEquivOfSurj_mk
    (c : RingCon M) {f : N →+* M} (hf : Function.Surjective f)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    c.comapQuotientEquivOfSurj f hf hcd x = f x := rfl
/-
**RingCon.comapQuotientEquivOfSurj_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] (c : RingCon M) {f : N →+* M}   (hf : Function.Surjective ⇑f) {d
 : RingCon N} (hcd : d = c.comap f) (x : N),   (c.comapQuotientEquivOfSurj f hf 
hcd).symm ↑(f x) = ↑x
参数：c : RingCon M；hf : Function.Surjective ⇑f；hcd : d = c.comap f；x : N；c.comapQu
otientEquivOfSurj f hf hcd；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingCon.comapQuotientEquivOfSurj_mk`：∀ {M : Type u_1} {N : Type u_2} [in
st : NonAssocSemiring M] [inst_1 : NonAssocSemiring N] (c : RingCon M) {f : N →+
* M}   (hf : Function.Sur…
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
@[simp] lemma comapQuotientEquivOfSurj_symm_mk
    (c : RingCon M) {f : N →+* M} (hf)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (c.comapQuotientEquivOfSurj f hf hcd).symm (f x) = x := by
  rw [← c.comapQuotientEquivOfSurj_mk hf hcd x, RingEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- This version infers the surjectivity of the function from a RingEquiv function -/
/-
**RingCon.comapQuotientEquivOfSurj_symm_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] (c : RingCon M) (f : N ≃+* M)   {d : RingCon N} (hcd : d = c.com
ap f) (x : N), (c.comapQuotientEquivOfSurj ↑f ⋯ hcd).symm ⟦f x⟧ = ↑x
参数：c : RingCon M；f : N ≃+* M；hcd : d = c.comap f；x : N；c.comapQuotientEquivOfSur
j ↑f ⋯ hcd。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingCon.comapQuotientEquivOfSurj_mk`：∀ {M : Type u_1} {N : Type u_2} [in
st : NonAssocSemiring M] [inst_1 : NonAssocSemiring N] (c : RingCon M) {f : N →+
* M}   (hf : Function.Sur…
· 使用定理 `RingEquiv.coe_toRingHom`：coe_toRingHom (f : R ≃+* S) : ⇑(f : R ->+* S) =
 f
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x

--- 原说明 ---
This version infers the surjectivity of the function from a RingEquiv function
-/
@[simp] lemma comapQuotientEquivOfSurj_symm_mk' (c : RingCon M) (f : N ≃+* M)
    {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (comapQuotientEquivOfSurj c (f : N →+* M) f.surjective hcd).symm ⟦f x⟧ = ↑x := by
  convert! RingEquiv.symm_apply_apply _ _
  rw [comapQuotientEquivOfSurj_mk, RingEquiv.coe_toRingHom]
  rfl

/-- The **second isomorphism theorem for semirings**. -/
/-
**RingCon.comapQuotientEquivRangeS** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：comapQuotientEquivRangeS (f : N ->+* M) {d : RingCon N} (hcd : d = comap c
 f) : d.Quotient ≃+* RingHom.rangeS (c.mk'.comp f)
参数：f : N ->+* M；hcd : d = comap c f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **second isomorphism theorem for semirings**.
-/
noncomputable def comapQuotientEquivRangeS (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) :
    d.Quotient ≃+* RingHom.rangeS (c.mk'.comp f) :=
  (RingCon.congr (.refl _) (hcd.trans comap_eq)).trans <| quotientKerEquivRangeS <| c.mk'.comp f
/-
**RingCon.comapQuotientEquivRangeS_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] (c : RingCon M) (f : N →+* M)   {d : RingCon N} (hcd : d = c.com
ap f) (x : N), (c.comapQuotientEquivRangeS f hcd) ↑x = ⟨↑(f x), ⋯⟩
参数：c : RingCon M；f : N →+* M；hcd : d = c.comap f；x : N；c.comapQuotientEquivRange
S f hcd；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
@[simp] theorem comapQuotientEquivRangeS_mk (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    c.comapQuotientEquivRangeS f hcd x = ⟨f x, (c.mk'.comp f).mem_rangeS_self x⟩ :=
  rfl
/-
**RingCon.comapQuotientEquivRangeS_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring N] (c : RingCon M) (f : N →+* M)   {d : RingCon N} (hcd : d = c.com
ap f) (x : N), (c.comapQuotientEquivRangeS f hcd).symm ⟨↑(f x), ⋯⟩ = ↑x
参数：c : RingCon M；f : N →+* M；hcd : d = c.comap f；x : N；c.comapQuotientEquivRange
S f hcd；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHom.mem_rangeS_self`：mem_rangeS_self (f : R ->+* S) (x : R) : f x in
 f.rangeS
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem comapQuotientEquivRangeS_symm_mk (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    (c.comapQuotientEquivRangeS f hcd).symm
      (⟨f x, RingHom.mem_rangeS_self (c.mk'.comp f) x ⟩) = x := by
  simp [RingEquiv.symm_apply_eq]

/-- The **third isomorphism theorem for (semi-)rings**. -/
/-
**RingCon.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientQuotientEquivQuotient (c d : RingCon M) (h : c <= d) : (RingCon.ke
r (c.map d h)).Quotient ≃+* d.Quotient
参数：c d : RingCon M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **third isomorphism theorem for (semi-)rings**.
-/
def quotientQuotientEquivQuotient (c d : RingCon M) (h : c ≤ d) :
    (RingCon.ker (c.map d h)).Quotient ≃+* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_add' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a + d.mk' b by rw [← d.mk'.map_add]; rfl
    map_mul' x y :=
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }
/-
**RingCon.quotientQuotientEquivQuotient_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon
`。
形式化陈述：∀ {M : Type u_1} [inst : NonAssocSemiring M] (c d : RingCon M) (h : c ≤ d)
 (x : M),   (c.quotientQuotientEquivQuotient d h) ⟦⟦x⟧⟧ = ⟦x⟧
参数：c d : RingCon M；h : c ≤ d；x : M；c.quotientQuotientEquivQuotient d h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem quotientQuotientEquivQuotient_mk_mk (c d : RingCon M) (h : c ≤ d) (x : M) :
    c.quotientQuotientEquivQuotient d h ⟦⟦x⟧⟧ = ⟦x⟧ := rfl
/-
**RingCon.quotientQuotientEquivQuotient_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingC
on`。
形式化陈述：∀ {M : Type u_1} [inst : NonAssocSemiring M] (c d : RingCon M) (h : c ≤ d)
 (x : M),   (c.quotientQuotientEquivQuotient d h) ↑↑x = ↑x
参数：c d : RingCon M；h : c ≤ d；x : M；c.quotientQuotientEquivQuotient d h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem quotientQuotientEquivQuotient_coe_coe (c d : RingCon M) (h : c ≤ d) (x : M) :
    c.quotientQuotientEquivQuotient d h ↑(x : c.Quotient) = x :=
  rfl
/-
**RingCon.quotientQuotientEquivQuotient_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingC
on`。
形式化陈述：∀ {M : Type u_1} [inst : NonAssocSemiring M] (c d : RingCon M) (h : c ≤ d)
 (x : M),   (c.quotientQuotientEquivQuotient d h).symm ⟦x⟧ = ⟦⟦x⟧⟧
参数：c d : RingCon M；h : c ≤ d；x : M；c.quotientQuotientEquivQuotient d h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem quotientQuotientEquivQuotient_symm_mk (c d : RingCon M) (h : c ≤ d) (x : M) :
    (c.quotientQuotientEquivQuotient d h).symm ⟦x⟧ = ⟦⟦x⟧⟧ :=
  rfl

end

section

variable [Ring M] [Ring N] [Ring P]

variable {c : RingCon M}

/-
**RingCon.range_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：range_mk' : RingHom.range c.mk' = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.range_eq_top`：range_eq_top {f : R ->+* S} : f.range = (⊤ : Subri
ng S) ↔ Function.Surjective f
· 使用定理 `RingCon.mk'_surjective`：∀ {R : Type u_1} [inst : NonAssocSemiring R] (c 
: RingCon R), Function.Surjective ⇑c.mk'
-/
theorem range_mk' : RingHom.range c.mk' = ⊤ :=
  RingHom.range_eq_top.mpr (mk'_surjective _)

variable {f : M →+* P}

/-- Given a congruence relation `c` on a ring and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
/-
**RingCon.range_lift** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : Ring M] [inst_1 : Ring P] {c : Rin
gCon M} {f : M →+* P} (H : c ≤ RingCon.ker f),   (c.lift f H).range = f.range
参数：H : c ≤ RingCon.ker f；c.lift f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_quot_lift`：range_quot_lift {r : ι -> ι -> Prop} (hf : forall x
 y, r x y -> f x = f y) : range (Quot.lift f hf) = range f

--- 原说明 ---
Given a congruence relation `c` on a ring and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient.
-/
@[simp] theorem range_lift (H : c ≤ ker f) :
    RingHom.range (c.lift f H) = f.range :=
  SetLike.coe_injective <| Set.range_quot_lift _

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
/-
**RingCon.kerLift_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : Ring M] [inst_1 : Ring P] {f : M →
+* P}, (RingCon.kerLift f).range = f.range
参数：RingCon.kerLift f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.range_lift`：∀ {M : Type u_1} {P : Type u_3} [inst : Ring M] [ins
t_1 : Ring P] {c : RingCon M} {f : M →+* P} (H : c ≤ RingCon.ker f),   (c.lift f
 H).rang…

--- 原说明 ---
Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`.
-/
@[simp] theorem kerLift_range_eq :
    RingHom.range (kerLift f) = RingHom.range f :=
  range_lift fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for rings**. -/
/-
**RingCon.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivRange (f : M ->+* P) : (ker f).Quotient ≃+* f.range
参数：f : M ->+* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem for rings**.
-/
noncomputable def quotientKerEquivRange (f : M →+* P) :
    (ker f).Quotient ≃+* f.range :=
  quotientKerEquivRangeS f

/-- The **second isomorphism theorem for rings**. -/
/-
**RingCon.comapQuotientEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：comapQuotientEquivRange (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap 
f) : d.Quotient ≃+* RingHom.range (c.mk'.comp f)
参数：f : N ->+* M；hcd : d = c.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **second isomorphism theorem for rings**.
-/
noncomputable def comapQuotientEquivRange (f : N →+* M) {d : RingCon N} (hcd : d = c.comap f) :
    d.Quotient ≃+* RingHom.range (c.mk'.comp f) :=
  c.comapQuotientEquivRangeS f hcd
/-
**RingCon.comapQuotientEquivRange_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comapQuotientEquivRange_mk (f : N ->+* M) {d : RingCon N} (hcd : d = c.com
ap f) (x : N) : c.comapQuotientEquivRange f hcd x = ⟨f x, (c.mk'.comp f).mem_ran
ge_self x⟩
参数：f : N ->+* M；hcd : d = c.comap f；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem comapQuotientEquivRange_mk
    (f : N →+* M) {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    c.comapQuotientEquivRange f hcd x = ⟨f x, (c.mk'.comp f).mem_range_self x⟩ :=
  rfl
/-
**RingCon.coe_comapQuotientEquivRange_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Ring M] [inst_1 : Ring N] (c : Rin
gCon M) (f : N →+* M) {d : RingCon N}   (hcd : d = c.comap f) (x : N), ↑((c.coma
pQuotientEquivRange f hcd) ↑x) = ↑(f x)
参数：c : RingCon M；f : N →+* M；hcd : d = c.comap f；x : N；(c.comapQuotientEquivRang
e f hcd) ↑x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
@[simp] theorem coe_comapQuotientEquivRange_mk
    (f : N →+* M) {d : RingCon N} (hcd : d = c.comap f) (x : N) :
    (c.comapQuotientEquivRange f hcd x) = (f x : c.Quotient) :=
  rfl
/-
**RingCon.comapQuotientEquivRange_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Ring M] [inst_1 : Ring N] (c : Rin
gCon M) (f : N →+* M) {d : RingCon N}   (hcd : d = c.comap f) (x : N), (c.comapQ
uotientEquivRange f hcd).symm ⟨↑(f x), ⋯⟩ = ↑x
参数：c : RingCon M；f : N →+* M；hcd : d = c.comap f；x : N；c.comapQuotientEquivRange
 f hcd；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHom.mem_range_self`：mem_range_self (f : R ->+* S) (x : R) : f x in f
.range
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem comapQuotientEquivRange_symm_mk (f : N →+* M)
    {d : RingCon N} (hcd : d = comap c f) (x : N) :
    (c.comapQuotientEquivRange f hcd).symm
      (⟨f x, RingHom.mem_range_self (c.mk'.comp f) x ⟩) = x := by
  simp [RingEquiv.symm_apply_eq, ← Subtype.coe_inj]

end

section

variable {R : Type*} [CommSemiring R]
  [Semiring M] [Algebra R M] [Semiring N] [Algebra R N] [Semiring P] [Algebra R P]

variable {c d : RingCon M} {f : M →ₐ[R] P}

set_option backward.isDefEq.respectTransparency.types false in
variable (R) in
/-- An isomorphism of algebras `e : M ≃ₐ[R] N` generates an isomorphism between quotient spaces,
if it is compatible with the relations. -/
/-
**RingCon.congr** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     [inst : NonAssocSemiring M] →     
  [inst_1 : NonAssocSemiring N] →         {c : RingCon M} → {d : RingCon N} → (e
 : M ≃+* N) → c = d.comap e → c.Quotient ≃+* d.Quotient
参数：e : M ≃+* N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of algebras `e : M ≃ₐ[R] N` generates an isomorphism between quot
ient spaces,
if it is compatible with the relations.
-/
protected def congrₐ {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) :
    c.Quotient ≃ₐ[R] d.Quotient where
  __ := RingCon.congr e h
  commutes' r := by simp [← coe_algebraMap]

@[simp]
/-
**RingCon.congr** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     [inst : NonAssocSemiring M] →     
  [inst_1 : NonAssocSemiring N] →         {c : RingCon M} → {d : RingCon N} → (e
 : M ≃+* N) → c = d.comap e → c.Quotient ≃+* d.Quotient
参数：e : M ≃+* N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrₐ_mk {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) (a : M) :
    RingCon.congrₐ R e h (a : c.Quotient) = (e a : d.Quotient) :=
  rfl
/-
**RingCon.congr** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     [inst : NonAssocSemiring M] →     
  [inst_1 : NonAssocSemiring N] →         {c : RingCon M} → {d : RingCon N} → (e
 : M ≃+* N) → c = d.comap e → c.Quotient ≃+* d.Quotient
参数：e : M ≃+* N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congrₐ_symm {c : RingCon M} {d : RingCon N} (e : M ≃ₐ[R] N) (h : c = d.comap e) :
    (RingCon.congrₐ R e h).symm =
      RingCon.congrₐ R e.symm (ext <| e.surjective.forall₂.2 <| by simp [h]) :=
  rfl
/-
**RingCon.range_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_mkₐ : AlgHom.range (mkₐ R c) = ⊤ :=
  (AlgHom.range_eq_top _).mpr (mkₐ_surjective _)

/-- The algebra homomorphism on the quotient of an algebra by a
congruence relation `c` induced by an algebra homomorphism
constant on the equivalence classes of `c`. -/
/-
**RingCon.lift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：lift (H : c <= ker f) : c.Quotient ->+* P where __
参数：H : c <= ker f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1

--- 原说明 ---
The algebra homomorphism on the quotient of an algebra by a
congruence relation `c` induced by an algebra homomorphism
constant on the equivalence classes of `c`.
-/
def liftₐ (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) :
    c.Quotient →ₐ[R] P :=
  { c.lift f H with
    commutes' r := AlgHomClass.commutes ↑f r }
/-
**RingCon.lift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：lift (H : c <= ker f) : c.Quotient ->+* P where __
参数：H : c <= ker f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem liftₐ_coe_toRingHom (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) :
    (c.liftₐ f H).toRingHom = c.lift f H :=
  rfl
/-
**RingCon.coe_lift** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftₐ (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) :
    ⇑(c.liftₐ f H) = c.lift f H :=
  rfl
/-
**RingCon.lift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：lift (H : c <= ker f) : c.Quotient ->+* P where __
参数：H : c <= ker f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
@[simp] theorem liftₐ_mk (c : RingCon M) (f : M →ₐ[R] P) (H : c ≤ ker f.toRingHom) (x : M) :
    c.liftₐ f H x = f x :=
  rfl

/-- Given a congruence relation `c` on an algebra and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient. -/
/-
**RingCon.lift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：lift (H : c <= ker f) : c.Quotient ->+* P where __
参数：H : c <= ker f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1

--- 原说明 ---
Given a congruence relation `c` on an algebra and a homomorphism `f`
constant on the equivalence classes of `c`, `f` has the same image
as the homomorphism that `f` induces on the quotient.
-/
theorem liftₐ_range (H : c ≤ ker f.toRingHom) :
    AlgHom.range (liftₐ c f H) = f.range :=
  Subalgebra.toSubsemiring_injective <| rangeS_lift H

/-- Homomorphisms on the quotient of a ring by a ring congruence relation are
equal if they are equal on elements that are coercions from the ring. -/
-- This should have higher priority than `AlgHom.ext`, but lower than any types implemented with
-- `Quotient`, as `ext` is lax with reducibility.
@[ext 1100]
/-
**RingCon.Quotient.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `RingCon.Quotient`。
形式化陈述：∀ {M : Type u_1} {P : Type u_3} [inst : NonAssocSemiring M] [inst_1 : NonA
ssocSemiring P] {c : RingCon M}   {f g : c.Quotient →+* P}, f.comp c.mk' = g.com
p c.mk' → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `RingCon.mk'_surjective`：∀ {R : Type u_1} [inst : NonAssocSemiring R] (c 
: RingCon R), Function.Surjective ⇑c.mk'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Quotient.hom_extₐ {f g : c.Quotient →ₐ[R] P}
    (h : f.comp (c.mkₐ R) = g.comp (c.mkₐ R)) : f = g :=
  DFunLike.ext _ _ <| c.mk'_surjective.forall.mpr fun x ↦ by exact congr($h x)

/-- `liftₐ` as an equivalence. -/
@[simps]
/-
**RingCon.lift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：lift (H : c <= ker f) : c.Quotient ->+* P where __
参数：H : c <= ker f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1

--- 原说明 ---
`liftₐ` as an equivalence.
-/
def liftₐEquiv (c : RingCon M) :
    { f : M →ₐ[R] P // c ≤ ker (f : M →+* P)} ≃ (c.Quotient →ₐ[R] P) where
  toFun f := liftₐ c f.1 f.2
  invFun F := ⟨F.comp (c.mkₐ R), fun x y h => congr(F $(Quotient.sound h))⟩

variable (f) in
/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
/-
**RingCon.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：kerLift : (ker f).Quotient ->+* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism induced on the quotient of a ring by the kernel of a ring homom
orphism.
-/
def kerLiftₐ : (ker f.toRingHom).Quotient →ₐ[R] P :=
  liftₐ (ker f.toRingHom) f (le_refl _)

/- Note : This can't be @[simp] because
  `(ker f.toRingHom).Quotient` is transformed into `(ker ↑f).Quotient`.
  Maybe `kerLiftₐ` should use the latter. -/
/-- The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes. -/
/-
**RingCon.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：kerLift : (ker f).Quotient ->+* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram described by the universal property for quotients of rings, when
the ring congruence relation is the kernel of the homomorphism, commutes.
-/
theorem kerLiftₐ_mk (x : M) : kerLiftₐ f x = f x := by
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
/-
**RingCon.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：kerLift : (ker f).Quotient ->+* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`
's kernel.
-/
theorem kerLiftₐ_injective (f : M →ₐ[R] P) :
    Injective (kerLiftₐ f) := kerLift_injective f.toRingHom

variable (R) in
/-- Given ring congruence relations `c, d` on an algebra such that `d`
contains `c`, `d`'s quotient map induces an algebra homomorphism from
the quotient by `c` to the quotient by `d`. -/
/-
**RingCon.factor** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given ring congruence relations `c, d` on an algebra such that `d`
contains `c`, `d`'s quotient map induces an algebra homomorphism from
the quotient by `c` to the quotient by `d`.
-/
def factorₐ {c d : RingCon M} (h : c ≤ d) :
    c.Quotient →ₐ[R] d.Quotient :=
  (liftₐ c (d.mkₐ R)) fun x y hc ↦ show (ker d.mk') x y from (ker_mk'_eq d).symm ▸ h hc

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
/-
**RingCon.factor** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map.
-/
theorem factorₐ_apply {c d : RingCon M} (h : c ≤ d) (x) :
    factorₐ R h x = liftₐ c (d.mkₐ R) (fun _ _ hc ↦ d.eq.2 <| h hc) x :=
  rfl

/-- Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map. -/
/-
**RingCon.factor** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given ring congruence relations `c, d` on a ring such that `d` contains `c`,
the definition of the homomorphism from the quotient by `c` to the quotient by
`d` induced by `d`'s quotient map.
-/
@[simp] theorem factorₐ_mk {c d : RingCon M} (h : c ≤ d) (x : M) :
    factorₐ R h ⟦x⟧ = ⟦x⟧ :=
  rfl
/-
**RingCon.mk** 是 Mathlib 中的一个ctor，位于命名空间 `RingCon`。
形式化陈述：{R : Type u_1} →   [inst : Add R] →     [inst_1 : Mul R] →       (toCon : 
Con R) →         (∀ {w x y z : R}, toCon.toSetoid w x → toCon.toSetoid y z → toC
on.toSetoid (w + y) (x + z)) → RingCon R
参数：toCon : Con R；∀ {w x y z : R}, toCon.toSetoid w x → toCon.toSetoid y z → toCo
n.toSetoid (w + y) (x + z)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mkₐ_comp_factorₐ_comp_mkₐ {c d : RingCon M} (h : c ≤ d) :
    (factorₐ R h).comp (c.mkₐ R) = d.mkₐ R :=
  rfl

/-- Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/
/-
**RingCon.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：kerLift : (ker f).Quotient ->+* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`.
-/
@[simp] theorem kerLiftₐ_range_eq :
    AlgHom.range (kerLiftₐ f) = AlgHom.range f :=
  liftₐ_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for algebra morphisms**. -/
/-
**RingCon.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivRange (f : M ->+* P) : (ker f).Quotient ≃+* f.range
参数：f : M ->+* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **first isomorphism theorem for algebra morphisms**.
-/
noncomputable def quotientKerEquivRangeₐ (f : M →ₐ[R] P) :
    (ker (f : M →+* P)).Quotient ≃ₐ[R] f.range where
  __ := AlgHom.codRestrict (kerLiftₐ f) _ _
  __ := quotientKerEquivRangeS f.toRingHom
/-
**RingCon.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivRange (f : M ->+* P) : (ker f).Quotient ≃+* f.range
参数：f : M ->+* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientKerEquivRangeₐ_mkₐ (f : M →ₐ[R] P) (x : M) :
    quotientKerEquivRangeₐ f x = ⟨f x, AlgHom.mem_range_self f x⟩ :=
  rfl

@[simp]
/-
**RingCon.coe_quotientKerEquivRange** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_quotientKerEquivRangeₐ_mkₐ (f : M →ₐ[R] P) (x : M) :
    (quotientKerEquivRangeₐ f x : P) = f x := by
  rfl
/-
**RingCon.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientKerEquivRange (f : M ->+* P) : (ker f).Quotient ≃+* f.range
参数：f : M ->+* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientKerEquivRangeₐ_comp_mkₐ (φ : M →ₐ[R] N) :
    ((quotientKerEquivRangeₐ φ).toAlgHom.comp ((ker (φ : M →+* N)).mkₐ R)) = φ.rangeRestrict :=
  rfl

/-- The **second isomorphism theorem for algebras**. -/
/-
**RingCon.comapQuotientEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：comapQuotientEquivRange (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap 
f) : d.Quotient ≃+* RingHom.range (c.mk'.comp f)
参数：f : N ->+* M；hcd : d = c.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **second isomorphism theorem for algebras**.
-/
noncomputable def comapQuotientEquivRangeₐ (f : N →ₐ[R] M) {d : RingCon N} (h : d = comap c f) :
    d.Quotient ≃ₐ[R] AlgHom.range ((c.mkₐ _).comp f) :=
  (RingCon.congrₐ R .refl (h.trans comap_eq)).trans <| quotientKerEquivRangeₐ ((c.mkₐ _).comp f)
/-
**RingCon.comapQuotientEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：comapQuotientEquivRange (f : N ->+* M) {d : RingCon N} (hcd : d = c.comap 
f) : d.Quotient ≃+* RingHom.range (c.mk'.comp f)
参数：f : N ->+* M；hcd : d = c.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapQuotientEquivRangeₐ_mk (f : N →ₐ[R] M) {d : RingCon N} (h : d = comap c f) (x : N) :
    c.comapQuotientEquivRangeₐ f h x = ⟨f x, AlgHom.mem_range_self _ x⟩ :=
  rfl
/-
**RingCon.coe_comapQuotientEquivRange** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_comapQuotientEquivRangeₐ_mk
    (f : N →ₐ[R] M) (x : N) {d : RingCon N} (h : d = comap c f) :
    (c.comapQuotientEquivRangeₐ f h x : c.Quotient) = f x :=
  rfl
/-
**RingCon.coe_comapQuotientEquivRange** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_comapQuotientEquivRangeₐ_symm_mk
    (f : N →ₐ[R] M) (x : N) {d : RingCon N} (h : d = c.comap f) :
    (c.comapQuotientEquivRangeₐ f h).symm (⟨f x, AlgHom.mem_range_self _ x⟩) = x := by
  simp [AlgEquiv.symm_apply_eq, ← Subtype.coe_inj]

variable (R)

/-- The **third isomorphism theorem for algebras**. -/
/-
**RingCon.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientQuotientEquivQuotient (c d : RingCon M) (h : c <= d) : (RingCon.ke
r (c.map d h)).Quotient ≃+* d.Quotient
参数：c d : RingCon M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **third isomorphism theorem for algebras**.
-/
def quotientQuotientEquivQuotientₐ {c d : RingCon M} (h : c ≤ d) :
    (RingCon.ker (factorₐ R h : c.Quotient →+* d.Quotient)).Quotient ≃ₐ[R] d.Quotient :=
  { quotientQuotientEquivQuotient c d h with
    commutes' _ := by rfl }

@[simp]
/-
**RingCon.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientQuotientEquivQuotient (c d : RingCon M) (h : c <= d) : (RingCon.ke
r (c.map d h)).Quotient ≃+* d.Quotient
参数：c d : RingCon M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientQuotientEquivQuotientₐ_mk_mk {c d : RingCon M} (h : c ≤ d) (x : M) :
    quotientQuotientEquivQuotientₐ R h ⟦⟦x⟧⟧ = ⟦x⟧ := rfl

@[simp]
/-
**RingCon.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientQuotientEquivQuotient (c d : RingCon M) (h : c <= d) : (RingCon.ke
r (c.map d h)).Quotient ≃+* d.Quotient
参数：c d : RingCon M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientQuotientEquivQuotientₐ_coe_coe {c d : RingCon M} (h : c ≤ d) (x : M) :
    quotientQuotientEquivQuotientₐ R h ↑(x : c.Quotient) = x :=
  quotientQuotientEquivQuotientₐ_mk_mk R h x

@[simp]
/-
**RingCon.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：quotientQuotientEquivQuotient (c d : RingCon M) (h : c <= d) : (RingCon.ke
r (c.map d h)).Quotient ≃+* d.Quotient
参数：c d : RingCon M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientQuotientEquivQuotientₐ_symm_mk {c d : RingCon M} (h : c ≤ d) (x : M) :
    (quotientQuotientEquivQuotientₐ R h).symm ⟦x⟧ = ⟦⟦x⟧⟧ :=
  rfl

end

end RingCon

