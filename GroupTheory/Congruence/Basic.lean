/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Congruence relations

This file proves basic properties of the quotient of a type by a congruence relation.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/

@[expose] public section


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section

variable [Mul M] [Mul N] [Mul P] (c : Con M)

variable {c}

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
`d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive prod /-- Given types with additions `M, N`, the product of two congruence relations
`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`
is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`. -/]
/-
**Con.prod** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：{M : Type u_1} → {N : Type u_2} → [inst : Mul M] → [inst_1 : Mul N] → Con 
M → Con N → Con (M × N)
参数：M × N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive /-- The product of an indexed collection of additive congruence relations. -/]
/-
**Con.pi** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：pi {ι : Type*} {f : ι -> Type*} [forall i, Mul (f i)] (C : forall i, Con (
f i)) : Con (forall i, f i)
参数：f i；C : forall i, Con (f i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of an indexed collection of congruence relations.
-/
def pi {ι : Type*} {f : ι → Type*} [∀ i, Mul (f i)] (C : ∀ i, Con (f i)) : Con (∀ i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

/-- A multiplicative equivalence `e : α ≃* β` generates an equivalence between quotient spaces,
if it is compatible with the relations. -/
@[to_additive
/-- An additive equivalence `e : α ≃+ β` generates an equivalence between quotient spaces,
if it is compatible with the relations. -/]
/-
**Con.congr** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     [inst : Mul M] →       [inst_1 : M
ul N] → {c : Con M} → {d : Con N} → (e : M ≃* N) → c = Con.comap ⇑e ⋯ d → c.Quot
ient ≃* d.Quotient
参数：e : M ≃* N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def congr {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) :
    c.Quotient ≃* d.Quotient where
  __ := Quotient.congr e <| by apply Con.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)

@[to_additive (attr := simp)]
/-
**Con.congr_mk** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：congr_mk {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul 
e)) (a : M) : Con.congr e h (a : c.Quotient) = (e a : d.Quotient)
参数：e : M ≃* N；h : c = d.comap e (map_mul e)；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem congr_mk {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) (a : M) :
    Con.congr e h (a : c.Quotient) = (e a : d.Quotient) := rfl

@[to_additive (attr := simp)]
/-
**Con.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：congr_symm {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mu
l e)) : (Con.congr e h).symm = Con.congr e.symm (ext <| e.surjective.forall₂.2 <
| by simp [h])
参数：e : M ≃* N；h : c = d.comap e (map_mul e)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem congr_symm {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) :
    (Con.congr e h).symm =
      Con.congr e.symm (ext <| e.surjective.forall₂.2 <| by simp [h]) :=
  rfl

@[to_additive]
/-
**Con.comap_conGen_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：comap_conGen_equiv {M N : Type*} [Mul M] [Mul N] (f : MulEquiv M N) (rel :
 N -> N -> Prop) : Con.comap f (map_mul f) (conGen rel) = conGen (fun x y => rel
 (f x) (f y))
参数：f : MulEquiv M N；rel : N -> N -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `MulEquiv.eq_symm_apply`：eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x 
↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Con.le_comap_conGen`：le_comap_conGen (r : N -> N -> Prop) (f : M -> N) (
hf) : conGen (r.onFun f) <= (conGen r).comap f hf
-/
theorem comap_conGen_equiv {M N : Type*} [Mul M] [Mul N] (f : MulEquiv M N) (rel : N → N → Prop) :
    Con.comap f (map_mul f) (conGen rel) = conGen (fun x y ↦ rel (f x) (f y)) := by
  apply le_antisymm _ (le_comap_conGen rel f (map_mul f))
  intro a b h
  simp only [Con.comap_rel] at h
  unfold Function.onFun
  generalize fa : f a = n1 at h
  generalize fb : f b = n2 at h
  induction h generalizing a b with
  | of x y h =>
    apply ConGen.Rel.of
    rwa [fa, fb]
  | refl x =>
    rw [f.injective (fa.trans fb.symm)]
    exact ConGen.Rel.refl _
  | symm _ h => exact ConGen.Rel.symm (h fb fa)
  | trans _ _ ih ih1 =>
    exact Exists.casesOn (f.surjective _) fun c' hc' ↦ ConGen.Rel.trans (ih fa hc') (ih1 hc' fb)
  | @mul w x y z _ _ ih ih1 =>
    rw [← f.eq_symm_apply, map_mul] at fa fb
    rw [fa, fb]
    exact ConGen.Rel.mul (ih (by simp) (by simp)) (ih1 (by simp) (by simp))

@[to_additive]
/-
**Con.comap_conGen_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：comap_conGen_of_bijective {M N : Type*} [Mul M] [Mul N] (f : M -> N) (hf :
 Function.Bijective f) (H : forall (x y : M), f (x * y) = f x * f y) (rel : N ->
 N -> Prop) : Con.comap f H (conGen rel) = conGen (fun x y => rel (f x) (f y))
参数：f : M -> N；hf : Function.Bijective f；H : forall (x y : M), f (x * y) = f x * 
f y；rel : N -> N -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.comap_conGen_equiv`：comap_conGen_equiv {M N : Type*} [Mul M] [Mul N]
 (f : MulEquiv M N) (rel : N -> N -> Prop) : Con.comap f (map_mul f) (conGen rel
) = conGen (…
-/
theorem comap_conGen_of_bijective {M N : Type*} [Mul M] [Mul N] (f : M → N)
    (hf : Function.Bijective f) (H : ∀ (x y : M), f (x * y) = f x * f y) (rel : N → N → Prop) :
    Con.comap f H (conGen rel) = conGen (fun x y ↦ rel (f x) (f y)) :=
  comap_conGen_equiv (MulEquiv.ofBijective (MulHom.mk f H) hf) rel

end

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] (c : Con M)

/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive (attr := coe) /-- The `AddSubmonoid` of `M × M` defined by an additive congruence
relation on an `AddMonoid` `M`. -/]
/-
**Con.submonoid** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：{M : Type u_1} → [inst : MulOneClass M] → Con M → Submonoid (M × M)
参数：M × M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def submonoid : Submonoid (M × M) where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul

variable {c}

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
is an equivalence relation. -/
@[to_additive /-- The additive congruence relation on an `AddMonoid` `M` from
an `AddSubmonoid` of `M × M` for which membership is an equivalence relation. -/]
/-
**Con.ofSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) in 
N) : Con M where r x y
参数：N : Submonoid (M × M)；H : Equivalence fun x y => (x, y) in N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) ∈ N) : Con M where
  r x y := (x, y) ∈ N
  iseqv := H
  mul' := N.mul_mem

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive /-- Coercion from a congruence relation `c` on an `AddMonoid` `M`
to the `AddSubmonoid` of `M × M` whose elements are `(x, y)` such that `x`
is related to `y` by `c`. -/]
/-
**Con.toSubmonoid** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：toSubmonoid : Coe (Con M) (Submonoid (M × M))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toSubmonoid : Coe (Con M) (Submonoid (M × M)) :=
  ⟨fun c => c.submonoid⟩

@[to_additive]
/-
**Con.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：mem_coe {c : Con M} {x y} : (x, y) in (↑c : Submonoid (M × M)) ↔ (x, y) in
 c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {c : Con M} {x y} : (x, y) ∈ (↑c : Submonoid (M × M)) ↔ (x, y) ∈ c :=
  Iff.rfl

@[to_additive]
/-
**Con.to_submonoid_inj** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：to_submonoid_inj (c d : Con M) (H : (c : Submonoid (M × M)) = d) : c = d
参数：c d : Con M；H : (c : Submonoid (M × M)) = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.ext`：ext {c d : Con M} (H : forall x y, c x y ↔ d x y) : c = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem to_submonoid_inj (c d : Con M) (H : (c : Submonoid (M × M)) = d) : c = d :=
  ext fun x y => show (x, y) ∈ c.submonoid ↔ (x, y) ∈ d from H ▸ Iff.rfl

@[to_additive]
/-
**Con.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：le_iff {c d : Con M} : c <= d ↔ (c : Submonoid (M × M)) <= d
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_iff {c d : Con M} : c ≤ d ↔ (c : Submonoid (M × M)) ≤ d :=
  ⟨fun h _ H => h H, fun h x y hc => h <| show (x, y) ∈ c from hc⟩

variable (x y : M)

@[to_additive (attr := simp)]
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): removed dot notation
/-
**Con.mrange_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：mrange_mk' : MonoidHom.mrange c.mk' = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.mrange_eq_top`：mrange_eq_top {f : F} : mrange f = (⊤ : Submono
id N) ↔ Surjective f
· 使用定理 `Con.mk'_surjective`：∀ {M : Type u_1} [inst : MulOneClass M] {c : Con M},
 Function.Surjective ⇑c.mk'
-/
theorem mrange_mk' : MonoidHom.mrange c.mk' = ⊤ :=
  MonoidHom.mrange_eq_top.2 mk'_surjective

variable {f : M →* P}

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
quotient. -/
@[to_additive /-- Given an additive congruence relation `c` on an `AddMonoid` and a homomorphism `f`
constant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces
on the quotient. -/]
/-
**Con.lift_range** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：lift_range (H : c <= ker f) : MonoidHom.mrange (c.lift f H) = MonoidHom.mr
ange f
参数：H : c <= ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
-/
theorem lift_range (H : c ≤ ker f) : MonoidHom.mrange (c.lift f H) = MonoidHom.mrange f :=
  Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
the same image as `f`. -/
@[to_additive (attr := simp) /-- Given an `AddMonoid` homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/]
/-
**Con.kerLift_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：kerLift_range_eq : MonoidHom.mrange (kerLift f) = MonoidHom.mrange f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.lift_range`：lift_range (H : c <= ker f) : MonoidHom.mrange (c.lift f
 H) = MonoidHom.mrange f
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem kerLift_range_eq : MonoidHom.mrange (kerLift f) = MonoidHom.mrange f :=
  lift_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for monoids**. -/
@[to_additive /-- The first isomorphism theorem for `AddMonoid`s. -/]
/-
**Con.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：quotientKerEquivRange (f : M ->* P) : (ker f).Quotient ≃* MonoidHom.mrange
 f
参数：f : M ->* P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Con.kerLift_range_eq`：kerLift_range_eq : MonoidHom.mrange (kerLift f) = 
MonoidHom.mrange f

--- 原说明 ---
The **first isomorphism theorem for monoids**.
-/
noncomputable def quotientKerEquivRange (f : M →* P) : (ker f).Quotient ≃* MonoidHom.mrange f :=
  { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.submonoidCongr kerLift_range_eq)).comp
        ⟨fun x y h =>
          kerLift_injective f <| by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
          fun ⟨w, z, hz⟩ => ⟨z, by rcases hz with ⟨⟩; rfl⟩⟩) with
    map_mul' := map_mul _ }

/-- The first isomorphism theorem for monoids in the case of a homomorphism with right inverse. -/
@[to_additive (attr := simps)
  /-- The first isomorphism theorem for `AddMonoid`s in the case of a homomorphism
  with right inverse. -/]
/-
**Con.quotientKerEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：quotientKerEquivOfRightInverse (f : M ->* P) (g : P -> M) (hf : Function.R
ightInverse g f) : (ker f).Quotient ≃* P
参数：f : M ->* P；g : P -> M；hf : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientKerEquivOfRightInverse (f : M →* P) (g : P → M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

/-- The first isomorphism theorem for Monoids in the case of a surjective homomorphism.

For a `computable` version, see `Con.quotientKerEquivOfRightInverse`.
-/
@[to_additive /-- The first isomorphism theorem for `AddMonoid`s in the case of a surjective
homomorphism.

For a `computable` version, see `AddCon.quotientKerEquivOfRightInverse`. -/]
/-
**Con.quotientKerEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：quotientKerEquivOfSurjective (f : M ->* P) (hf : Surjective f) : (ker f).Q
uotient ≃* P
参数：f : M ->* P；hf : Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def quotientKerEquivOfSurjective (f : M →* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c : Con N -/
@[to_additive /-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c :
AddCon N -/]
/-
**Con.comapQuotientEquivOfSurj** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：comapQuotientEquivOfSurj (c : Con M) (f : N ->* M) (hf : Function.Surjecti
ve f) : (Con.comap f f.map_mul c).Quotient ≃* c.Quotient
参数：c : Con M；f : N ->* M；hf : Function.Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Con.comap_eq`：comap_eq {f : N ->* M} : comap f f.map_mul c = ker (c.mk'.
comp f)
-/
noncomputable def comapQuotientEquivOfSurj (c : Con M) (f : N →* M) (hf : Function.Surjective f) :
    (Con.comap f f.map_mul c).Quotient ≃* c.Quotient :=
  (Con.congr (.refl _) Con.comap_eq).trans <| Con.quotientKerEquivOfSurjective (c.mk'.comp f) <|
    Con.mk'_surjective.comp hf

@[to_additive (attr := simp)]
/-
**Con.comapQuotientEquivOfSurj_mk** 是 Mathlib 中的一个引理，位于命名空间 `Con`。
形式化陈述：comapQuotientEquivOfSurj_mk (c : Con M) {f : N ->* M} (hf : Function.Surje
ctive f) (x : N) : comapQuotientEquivOfSurj c f hf x = f x
参数：c : Con M；hf : Function.Surjective f；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
lemma comapQuotientEquivOfSurj_mk (c : Con M) {f : N →* M} (hf : Function.Surjective f) (x : N) :
    comapQuotientEquivOfSurj c f hf x = f x := rfl

@[to_additive (attr := simp)]
/-
**Con.comapQuotientEquivOfSurj_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 `Con`。
形式化陈述：comapQuotientEquivOfSurj_symm_mk (c : Con M) {f : N ->* M} (hf) (x : N) : 
(comapQuotientEquivOfSurj c f hf).symm (f x) = x
参数：c : Con M；hf；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MulEquiv.symm_apply_eq`：symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y 
↔ x = e y
-/
lemma comapQuotientEquivOfSurj_symm_mk (c : Con M) {f : N →* M} (hf) (x : N) :
    (comapQuotientEquivOfSurj c f hf).symm (f x) = x :=
  (MulEquiv.symm_apply_eq (c.comapQuotientEquivOfSurj f hf)).mpr rfl

set_option backward.isDefEq.respectTransparency false in
/-- This version infers the surjectivity of the function from a MulEquiv function -/
@[to_additive (attr := simp) /-- This version infers the surjectivity of the function from a
MulEquiv function -/]
/-
**Con.comapQuotientEquivOfSurj_symm_mk'** 是 Mathlib 中的一个引理，位于命名空间 `Con`。
形式化陈述：comapQuotientEquivOfSurj_symm_mk' (c : Con M) (f : N ≃* M) (x : N) : ((@Mu
lEquiv.symm (Con.Quotient (comap ⇑f _ c)) _ _ _ (comapQuotientEquivOfSurj c (f :
 N ->* M) f.surjective)) ⟦f x⟧) = ↑x
参数：c : Con M；f : N ≃* M；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `MulEquiv.symm_apply_eq`：symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y 
↔ x = e y
-/
lemma comapQuotientEquivOfSurj_symm_mk' (c : Con M) (f : N ≃* M) (x : N) :
    ((@MulEquiv.symm (Con.Quotient (comap ⇑f _ c)) _ _ _
      (comapQuotientEquivOfSurj c (f : N →* M) f.surjective)) ⟦f x⟧) = ↑x :=
  (MulEquiv.symm_apply_eq (@comapQuotientEquivOfSurj M N _ _ c f _)).mpr rfl

/-- The **second isomorphism theorem for monoids**. -/
@[to_additive /-- The second isomorphism theorem for `AddMonoid`s. -/]
/-
**Con.comapQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：comapQuotientEquiv (f : N ->* M) : (comap f f.map_mul c).Quotient ≃* Monoi
dHom.mrange (c.mk'.comp f)
参数：f : N ->* M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Con.comap_eq`：comap_eq {f : N ->* M} : comap f f.map_mul c = ker (c.mk'.
comp f)

--- 原说明 ---
The **second isomorphism theorem for monoids**.
-/
noncomputable def comapQuotientEquiv (f : N →* M) :
    (comap f f.map_mul c).Quotient ≃* MonoidHom.mrange (c.mk'.comp f) :=
  (Con.congr (.refl _) comap_eq).trans <| quotientKerEquivRange <| c.mk'.comp f

/-- The **third isomorphism theorem for monoids**. -/
@[to_additive /-- The third isomorphism theorem for `AddMonoid`s. -/]
/-
**Con.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：quotientQuotientEquivQuotient (c d : Con M) (h : c <= d) : (ker (c.map d h
)).Quotient ≃* d.Quotient
参数：c d : Con M；h : c <= d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **third isomorphism theorem for monoids**.
-/
def quotientQuotientEquivQuotient (c d : Con M) (h : c ≤ d) :
    (ker (c.map d h)).Quotient ≃* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

end MulOneClass

section Monoids

@[to_additive]
/-
**Con.smul** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : C
on M) (a : α) {w x : M} (h : c w x) : c (a • w) (a • x)
参数：c : Con M；a : α；h : c w x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
-/
theorem smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
    {w x : M} (h : c w x) : c (a • w) (a • x) := by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • (1 : M) : M)) h

end Monoids

section Actions

@[to_additive]
/-
**Con.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：instSMul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c
 : Con M) : SMul α c.Quotient where smul a
参数：c : Con M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Con.smul`：smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α
 M M] (c : Con M) (a : α) {w x : M} (h : c w x) : c (a • w) (a • x)
-/
instance instSMul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) :
    SMul α c.Quotient where
  smul a := (Quotient.map' (a • ·)) fun _ _ => c.smul a

@[to_additive]
/-
**Con.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c
 : Con M) (a : α) (x : M) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient)
参数：c : Con M；a : α；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M)
    (a : α) (x : M) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl
/-
**Con.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：instSMulCommClass {α β M : Type*} [MulOneClass M] [SMul α M] [SMul β M] [I
sScalarTower α M M] [IsScalarTower β M M] [SMulCommClass α β M] (c : Con M) : SM
ulCommClass α β c.Quotient where smul_comm a b
参数：c : Con M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass {α β M : Type*} [MulOneClass M] [SMul α M] [SMul β M]
    [IsScalarTower α M M] [IsScalarTower β M M] [SMulCommClass α β M] (c : Con M) :
    SMulCommClass α β c.Quotient where
  smul_comm a b := Quotient.ind' fun m => congr_arg Quotient.mk'' <| smul_comm a b m
/-
**Con.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：instIsScalarTower {α β M : Type*} [MulOneClass M] [SMul α β] [SMul α M] [S
Mul β M] [IsScalarTower α M M] [IsScalarTower β M M] [IsScalarTower α β M] (c : 
Con M) : IsScalarTower α β c.Quotient where smul_assoc a b
参数：c : Con M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower {α β M : Type*} [MulOneClass M] [SMul α β] [SMul α M] [SMul β M]
    [IsScalarTower α M M] [IsScalarTower β M M] [IsScalarTower α β M] (c : Con M) :
    IsScalarTower α β c.Quotient where
  smul_assoc a b := Quotient.ind' fun m => congr_arg Quotient.mk'' <| smul_assoc a b m
/-
**Con.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：instIsCentralScalar {α M : Type*} [MulOneClass M] [SMul α M] [SMul αᵐᵒᵖ M]
 [IsScalarTower α M M] [IsScalarTower αᵐᵒᵖ M M] [IsCentralScalar α M] (c : Con M
) : IsCentralScalar α c.Quotient where op_smul_eq_smul a
参数：c : Con M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar {α M : Type*} [MulOneClass M] [SMul α M] [SMul αᵐᵒᵖ M]
    [IsScalarTower α M M] [IsScalarTower αᵐᵒᵖ M M] [IsCentralScalar α M] (c : Con M) :
    IsCentralScalar α c.Quotient where
  op_smul_eq_smul a := Quotient.ind' fun m => congr_arg Quotient.mk'' <| op_smul_eq_smul a m

@[to_additive]
/-
**Con.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：mulAction {α M : Type*} [Monoid α] [MulOneClass M] [MulAction α M] [IsScal
arTower α M M] (c : Con M) : MulAction α c.Quotient where one_smul
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction {α M : Type*} [Monoid α] [MulOneClass M] [MulAction α M] [IsScalarTower α M M]
    (c : Con M) : MulAction α c.Quotient where
  one_smul := Quotient.ind' fun _ => congr_arg Quotient.mk'' <| one_smul _ _
  mul_smul _ _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' <| mul_smul _ _ _
/-
**Con.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：mulDistribMulAction {α M : Type*} [Monoid α] [Monoid M] [MulDistribMulActi
on α M] [IsScalarTower α M M] (c : Con M) : MulDistribMulAction α c.Quotient
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction {α M : Type*} [Monoid α] [Monoid M] [MulDistribMulAction α M]
    [IsScalarTower α M M] (c : Con M) : MulDistribMulAction α c.Quotient :=
  { smul_one := fun _ => congr_arg Quotient.mk'' <| smul_one _
    smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' <| smul_mul' _ _ _ }

end Actions

end Con

