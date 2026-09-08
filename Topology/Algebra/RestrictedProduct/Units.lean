/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Units of restricted products

This file contains results about the units of a restricted product. The restricted
product `Πʳ i : ι, [R i, B i]_[𝓕]` of a family of types `R` with respect to a family of
subsets `B` along a filter `𝓕` is defined in `Mathlib.Topology.Algebra.RestrictedProduct.Basic`.
Here, we give conditions that characterize when an element of the restricted product is a unit,
and provide an isomorphism between the units of the restricted product and the restricted product
of the units.

## Main definitions

* `RestrictedProduct.unitsEquiv`: the (monoid) isomorphism between `(Πʳ i, [R i, B i]_[𝓕])ˣ`
  and `Πʳ i, [(R i)ˣ, (B i).units]_[𝓕]`.

## Tags

restricted product, adeles, ideles
-/

@[expose] public section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} [∀ i, Monoid (R i)]
variable {S : ι → Type*} [Π i, SetLike (S i) (R i)] [∀ (i : ι), SubmonoidClass (S i) (R i)]
variable {B : Π i, S i}
variable {𝓕 : Filter ι}

/-
**RestrictedProduct.isUnit_of_eventually_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Restr
ictedProduct`。
形式化陈述：isUnit_of_eventually_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : forall i, IsU
nit (x i)) (hxr : forallᶠ i in 𝓕, exists (h : x i in B i), IsUnit (⟨x i, h⟩ : B 
i)) : IsUnit x
参数：hx : forall i, IsUnit (x i)；hxr : forallᶠ i in 𝓕, exists (h : x i in B i), Is
Unit (⟨x i, h⟩ : B i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.eq_inv_of_mul_eq_one_left`：∀ {α : Type u} [inst : Monoid α] {u : α
ˣ} {a : α}, ↑u * a = 1 → a = ↑u⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isUnit_of_eventually_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : ∀ i, IsUnit (x i))
    (hxr : ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i)) :
    IsUnit x := by
  rw [isUnit_iff_exists]
  use .mk (fun i ↦ (hx i).unit.inv) (by
    filter_upwards [hxr] with i ⟨h, hu⟩
    have hu : (hx i).unit.1 * hu.unit.inv = 1 := Subtype.val_inj.2 hu.mul_val_inv
    simp [← Units.eq_inv_of_mul_eq_one_left hu])
  simp [RestrictedProduct.ext_iff]
/-
**RestrictedProduct.eventually_isUnit_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Restr
ictedProduct`。
形式化陈述：eventually_isUnit_of_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x) : (
forall i, IsUnit (x i)) ∧ forallᶠ i in 𝓕, exists (h : x i in B i), IsUnit (⟨x i,
 h⟩ : B i)
参数：hx : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.skolem`：∀ {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → P
rop}, (∀ (x : α), ∃ y, p x y) ↔ ∃ f, ∀ (x : α), p x (f x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem eventually_isUnit_of_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x) :
    (∀ i, IsUnit (x i)) ∧ ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i) := by
  simp only [isUnit_iff_exists, RestrictedProduct.ext_iff, ← forall_and] at hx
  simp only [isUnit_iff_exists]
  choose b hb using hx
  exact ⟨Classical.skolem.symm.1 ⟨b, hb⟩, by filter_upwards [x.2, b.2] using
    fun i hx hb ↦ ⟨hx, ⟨b i, hb⟩, by simp_all [← SetLike.coe_eq_coe]⟩⟩

@[deprecated (since := "2026-04-06")]
alias eventualy_isUnit_of_isUnit := eventually_isUnit_of_isUnit
/-
**RestrictedProduct.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduct`。
形式化陈述：isUnit_iff {x : Πʳ i, [R i, B i]_[𝓕]} : IsUnit x ↔ (forall i, IsUnit (x i)
) ∧ forallᶠ i in 𝓕, exists (h : x i in B i), IsUnit (⟨x i, h⟩ : B i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RestrictedProduct.eventually_isUnit_of_isUnit`：eventually_isUnit_of_isUn
it {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x) : (forall i, IsUnit (x i)) ∧ foral
lᶠ i in 𝓕, exists (h : x i in B i),…
· 使用定理 `RestrictedProduct.isUnit_of_eventually_isUnit`：isUnit_of_eventually_isUn
it {x : Πʳ i, [R i, B i]_[𝓕]} (hx : forall i, IsUnit (x i)) (hxr : forallᶠ i in 
𝓕, exists (h : x i in B i), IsUnit …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isUnit_iff {x : Πʳ i, [R i, B i]_[𝓕]} :
    IsUnit x ↔ (∀ i, IsUnit (x i)) ∧ ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i) :=
  ⟨eventually_isUnit_of_isUnit, fun h ↦ isUnit_of_eventually_isUnit h.1 h.2⟩

/-- The homomorphism from the units of a restricted product to the regular product of unit. -/
/-
**RestrictedProduct.coeUnits** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：coeUnits : Πʳ i, [R i, B i]_[𝓕]ˣ ->* (i : ι) -> (R i)ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism from the units of a restricted product to the regular product o
f unit.
-/
def coeUnits : Πʳ i, [R i, B i]_[𝓕]ˣ →* (i : ι) → (R i)ˣ :=
  MulEquiv.piUnits.toMonoidHom.comp <| Units.map coeMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- Constructs a unit in a restricted product `Πʳ i, [R i, B i]_[𝓕]` given an element `x` of
the usual product and the condition that `x` is eventually in the units of `B i` along `𝓕`. -/
/-
**RestrictedProduct.mkUnit** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：mkUnit (x : Π i, (R i)ˣ) (hx : forallᶠ i in 𝓕, x i in (Submonoid.ofClass (
B i)).units) : Πʳ i, [R i, B i]_[𝓕]ˣ where val
参数：x : Π i, (R i)ˣ；hx : forallᶠ i in 𝓕, x i in (Submonoid.ofClass (B i)).units。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a unit in a restricted product `Πʳ i, [R i, B i]_[𝓕]` given an elemen
t `x` of
the usual product and the condition that `x` is eventually in the units of `B i`
 along `𝓕`.
-/
def mkUnit (x : Π i, (R i)ˣ) (hx : ∀ᶠ i in 𝓕, x i ∈ (Submonoid.ofClass (B i)).units) :
    Πʳ i, [R i, B i]_[𝓕]ˣ where
  val := ⟨fun i ↦ (x i).1, by filter_upwards [hx] using fun i hi ↦ hi.1⟩
  inv := ⟨fun i ↦ (x i)⁻¹.1, by filter_upwards [hx] using fun i hi ↦ hi.2⟩
  val_inv := by ext; simp
  inv_val := by ext; simp

variable (R) in
/-- The ring isomorphism between the units of a restricted product `Πʳ i, [R i, B i]_[𝓕]` and
the restricted product of `(R i)ˣ` with respect to `(B i)ˣ`. -/
/-
**RestrictedProduct.unitsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RestrictedProduct`。
形式化陈述：unitsEquiv : Πʳ i, [R i, B i]_[𝓕]ˣ ≃* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B
 i)).units]_[𝓕] where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring isomorphism between the units of a restricted product `Πʳ i, [R i, B i]
_[𝓕]` and
the restricted product of `(R i)ˣ` with respect to `(B i)ˣ`.
-/
def unitsEquiv : Πʳ i, [R i, B i]_[𝓕]ˣ ≃* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓕] where
  toFun x := ⟨coeUnits x, by filter_upwards [x.val.2, x.inv.2] using fun i hi hi' ↦ ⟨hi, hi'⟩⟩
  invFun y := mkUnit y.1 y.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
/-
**RestrictedProduct.unitsEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedProduc
t`。
形式化陈述：∀ {ι : Type u_1} {R : ι → Type u_2} [inst : (i : ι) → Monoid (R i)] {S : ι
 → Type u_3}   [inst_1 : (i : ι) → SetLike (S i) (R i)] [inst_2 : ∀ (i : ι), Sub
monoidClass (S i) (R i)] {B : (i : ι) → S i}   {𝓕 : Filter ι} (i : ι) (x : (Rest
rictedProduct (fun i => R i) (fun i => ↑(B i)) 𝓕)ˣ),   ↑(((RestrictedProduct.uni
tsEquiv R) x) i) = ↑x i
参数：i : ι；R i；i : ι；S i；R i；i : ι；S i；R i；i : ι；i : ι；x : (RestrictedProduct (fun
 i => R i) (fun i => ↑(B i)) 𝓕)ˣ；((RestrictedProduct.unitsEquiv R) x) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
@[simp] lemma unitsEquiv_apply (i : ι) (x : Πʳ i, [R i, B i]_[𝓕]ˣ) :
    (unitsEquiv R x i) = x.1 i := rfl
/-
**RestrictedProduct.coe_unitsEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `RestrictedPr
oduct`。
形式化陈述：∀ {ι : Type u_1} {R : ι → Type u_2} [inst : (i : ι) → Monoid (R i)] {S : ι
 → Type u_3}   [inst_1 : (i : ι) → SetLike (S i) (R i)] [inst_2 : ∀ (i : ι), Sub
monoidClass (S i) (R i)] {B : (i : ι) → S i}   {𝓕 : Filter ι} (x : (RestrictedPr
oduct (fun i => R i) (fun i => ↑(B i)) 𝓕)ˣ) (i : ι),   ↑((RestrictedProduct.unit
sEquiv R) x) i = ((RestrictedProduct.unitsEquiv R) x) i
参数：i : ι；R i；i : ι；S i；R i；i : ι；S i；R i；i : ι；x : (RestrictedProduct (fun i => 
R i) (fun i => ↑(B i)) 𝓕)ˣ；i : ι；(RestrictedProduct.unitsEquiv R) x；(RestrictedP
roduct.unitsEquiv R) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
@[simp] lemma coe_unitsEquiv_apply (x : Πʳ i, [R i, B i]_[𝓕]ˣ) (i : ι) :
    (unitsEquiv R x).1 i = unitsEquiv R x i := rfl

end RestrictedProduct

